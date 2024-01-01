use arecibo::provider::{PallasEngine, VestaEngine};
use arecibo::traits::circuit::StepCircuit;
use arecibo::traits::Group;
use bellpepper_core::ConstraintSystem;
use circom_scotia::{calculate_witness, r1cs::CircomConfig};
use ff::Field;
use std::cmp::min;
use std::env::current_dir;

use crate::utils::{self, n_blocks_from_bytes, pad_vector_to_min_length};

type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = arecibo::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

const N_KEYS: usize = 8;
const N_MESSAGE_WORDS_BLOCK: usize = 16;
const MAX_BLOCKS_PER_CHUNK: usize = 16;
const MAX_BYTES_PER_BLOCK: usize = 64;

const IV: [u32; N_KEYS] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

struct Blake3CompressPublicParams<G : Group> {
	additional_flags_out: G::Scalar,	
	n_blocks_out: G::Scalar,
	block_count_out: G::Scalar,
	h_out: [G::Scalar; 8],
}

#[derive(Clone, Debug)]
pub struct Blake3BlockCompressCircuit<G: Group> {
    bytes: Vec<u8>,
    // TODO: update circom accordingly
    n_bytes: usize,
    current_block: usize,
    _p: std::marker::PhantomData<G>,
}

impl<G: Group> Blake3CompressPublicParams<G> {
	fn from_vec(vec: Vec<G::Scalar>) -> Blake3CompressPublicParams<G> {
		assert!(vec.len() == 11);
		let additional_flags_out = vec[0];
		let n_blocks_out = vec[1];
		let block_count_out = vec[2];
		let h_out = [vec[3], vec[4], vec[5], vec[6], vec[7], vec[8], vec[9], vec[10]];
		Blake3CompressPublicParams {
			additional_flags_out,
			n_blocks_out,
			block_count_out,
			h_out,
		}
	}
}

impl<G: Group> Blake3BlockCompressCircuit<G> {
    pub fn new(bytes: Vec<u8>) -> Blake3BlockCompressCircuit<G> {
        // TODO: ceiling
        // We need to check that the ceiling of the bytes split up into 4-byte words
        // is less than or equal to the max number of blocks per chunk.
        assert!(
            bytes.len() <= MAX_BYTES_PER_BLOCK * MAX_BLOCKS_PER_CHUNK,
            "Too many bytes per chunk"
        );

        let bytes_len = bytes.len();
        Blake3BlockCompressCircuit {
            n_bytes: bytes_len,
            bytes,
            // TODO: it aint actually chunk len
            current_block: 0,
            _p: std::marker::PhantomData,
        }
    }

    pub fn update_for_step(&mut self) -> () {
        self.current_block += 1;
    }

    fn format_input(
        &self,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<(String, Vec<G::Scalar>)>, bellpepper_core::SynthesisError> {
        // TODO: formailize mapping?

        // 4 bytes per 32-bit word
        let start_idx = self.current_block * 4 * 16;
        println!(
            "Start idx: {} and current block: {}",
            start_idx, self.current_block
        );
        let end_idx = min(start_idx + 4 * 16, self.n_bytes);

        let mut message_bytes = self.bytes[start_idx..end_idx].to_vec();
        // The number of 32 bit words (4 byte) in the message
        pad_vector_to_min_length(&mut message_bytes, MAX_BYTES_PER_BLOCK, 0);
        let as_u32 = utils::bytes_to_u32_le(&message_bytes);

        let message_block_scalar = as_u32.iter().map(|x| G::Scalar::from(*x as u64)).collect();

        let n_bytes = (end_idx - start_idx) as u64;
        println!(
            "n_bytes: {}. Start: {}, End: {}",
            n_bytes, start_idx, end_idx
        );
        assert!(
            n_bytes <= MAX_BYTES_PER_BLOCK as u64,
            "Too many bytes per block"
        );
        // The number of bytes
        let b = G::Scalar::from(n_bytes);

        println!("z boys: {}", z.len());
        let n_blocks_calc = n_blocks_from_bytes(self.n_bytes) as u64;

        let n_blocks = z[0]
            .clone()
            .get_value()
            .unwrap_or(G::Scalar::from(n_blocks_calc));

        let current_block = z[1].clone().get_value().unwrap_or_else(|| {
            println!("DOING THE OR ELSE OF UNWRAP");
            G::Scalar::ZERO
        });

        let keys = z[2..10]
            .to_vec()
            .iter()
            .map(|x| {
                x.clone().get_value().unwrap_or(
                    G::Scalar::ZERO, // TODO: IDK WITH THESE
                )
            })
            .collect::<Vec<_>>();

        let b_arg = ("b".to_string(), vec![b]);
        let msg_arg = ("m".into(), message_block_scalar);
        let key_args = ("h".into(), keys);
        let current_block_arg = ("block_count".into(), vec![current_block]);
        let n_block_args = ("n_blocks".into(), vec![n_blocks]);

        // OHHH THIS IS LITERALLY THEE ARGS IN
        // TODO: we also need to **load** the private witness here.
        let input = vec![b_arg, msg_arg, key_args, current_block_arg, n_block_args];
        Ok(input)
    }
}

impl<G: Group> StepCircuit<G::Scalar> for Blake3BlockCompressCircuit<G> {
    fn arity(&self) -> usize {
        // + 2 refers to the d flag and b block size
        // TODO: IDK
        N_KEYS + 2
        // N_KEYS + N_MESSAGE_WORDS_BLOCK + 2
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<G::Scalar>>, bellpepper_core::SynthesisError>
    {
        let root = current_dir().unwrap().join("../build/");
        println!("The current directory is {}", root.display());

        // TODO: make these a thing...
        // TODO: RIP. WE NEED THE WITNESS TO GENERATE AUTO-MAGICALLY HERE.
        // TODO: maybe this should be within new? Like why remake it with each synthesize?
        let wtns = root.join("blake3_nova_js/blake3_nova.wasm");
        let r1cs = root.join("blake3_nova.r1cs");

        let cfg = CircomConfig::<G::Scalar>::new(wtns, r1cs).unwrap();
        println!("Loaded config for R1CS");

        let witness = calculate_witness(&cfg, input, true).expect("msg");

        utils::synthesize_with_vec::<G::Scalar, _>(
            &mut cs.namespace(|| "blake3_circom"),
            cfg.r1cs.clone(),
            Some(witness),
            // Return the arity of the input/output for the public ins and outs
            self.arity(),
        )
    }
}
