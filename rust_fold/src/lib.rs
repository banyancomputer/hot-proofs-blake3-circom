use arecibo::provider::{PallasEngine, VestaEngine};
use arecibo::traits::circuit::StepCircuit;
use arecibo::traits::circuit::TrivialCircuit;
use arecibo::traits::snark::RelaxedR1CSSNARKTrait;
use arecibo::traits::Engine;
use arecibo::traits::Group;
use arecibo::CompressedSNARK;
use arecibo::PublicParams;
use arecibo::RecursiveSNARK;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use circom_scotia::{calculate_witness, r1cs::CircomConfig, synthesize};
use ff::{Field, PrimeField};
use std::cmp::{max, min};
use std::env::current_dir;
use std::time::Instant;

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

mod utils;

const IV: [u32; N_KEYS] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

/// A single iteration of the blake3 block compression function.
/// Everything is little-endian.
#[derive(Clone, Debug)]
struct Blake3BlockCompressIteration<G: Group> {
    /// The key for this block (h_0, ..., h_7).
    keys: [G::Scalar; N_KEYS],
    // /// The message set for this block (m_0, ..., m_15).
    // message: [G::Scalar; N_MESSAGE_WORDS_BLOCK],
    /// Starting value for the d flag.
    // d_base: G::Scalar,
    block_count: G::Scalar,
}

#[derive(Clone, Debug)]
struct Blake3BlockCompressCircuit<G: Group> {
    // seq: Vec<Blake3BlockCompressIteration<G>>,
    start: Blake3BlockCompressIteration<G>,
    bytes: Vec<u8>,
    // TODO: update circom accordingly
    n_bytes: usize,
    current_block: usize,
}

impl<G: Group> Blake3BlockCompressCircuit<G> {
    fn new(bytes: Vec<u8>) -> Blake3BlockCompressCircuit<G> {
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
            start: Blake3BlockCompressIteration {
                // Convert the IV to G::Scalar.
                keys: IV
                    .iter()
                    .map(|x| G::Scalar::from(*x as u64))
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
                // d_base: <E1 as Engine>::Scalar::zero(),
                block_count: G::Scalar::ZERO,
            },
            current_block: 0,
        }
    }
    fn update_for_step(&mut self) -> () {
        self.current_block += 1;
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

        // TODO: formailize mapping?

        // let curr_block_val = current_block.get_value().unwrap()
        // 4 bytes per 32-bit word
        let start_idx = self.current_block * 4 * 16;
        let end_idx = min(start_idx + 4 * 16, self.n_bytes);

        let message_bytes = self.bytes[start_idx..end_idx].to_vec();
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
        let n_blocks_calc = (self.n_bytes / MAX_BYTES_PER_BLOCK) as u64;
        // TODO: WHAT?
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

/// Using folding to prove that the prover knows all the preimages of blocks in a file
/// and that they chain together correctly.
fn prove_chunk_hash(bytes: Vec<u8>) {
    // TODO: I think that we need to add padding stuff in somewhere (like in the circom or something?)
    println!("Nova-based Blake3 Chunk Compression");
    println!("=========================================================");

    let num_steps = N_MESSAGE_WORDS_BLOCK;
    // number of iterations of MinRoot per Nova's recursive step
    let mut circuit_primary = Blake3BlockCompressCircuit::new(bytes);
    let circuit_secondary = TrivialCircuit::default();
    println!(
        "Proving {} bytes of Blake3Compress per step",
        circuit_primary.n_bytes
    );

    // produce public parameters
    let start = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
    >::setup(
        &circuit_primary,
        &circuit_secondary,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    );
    println!("PublicParams::setup, took {:?} ", start.elapsed());

    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    let mut z0_primary = Vec::new();

    // Round up
    let n_blocks = (circuit_primary.n_bytes + MAX_BYTES_PER_BLOCK - 1) / MAX_BYTES_PER_BLOCK;
    // Push n_blocks to be the first element of the primary witness
    z0_primary.push(<E1 as Engine>::Scalar::from(n_blocks as u64));
    // Push 0 for current block
    z0_primary.push(<E1 as Engine>::Scalar::zero());
    z0_primary.extend_from_slice(&circuit_primary.start.keys);

    // produce non-deterministic advice
    // let (z0_primary, minroot_iterations) = MinRootIteration::<<E1 as Engine>::GE>::new(
    //     num_iters_per_step * num_steps,
    //     &<E1 as Engine>::Scalar::zero(),
    //     &<E1 as Engine>::Scalar::one(),
    // );
    // TODO: WHAT?
    // let minroot_circuits = (0..num_steps)
    //     .map(|i| MinRootCircuit {
    //         seq: (0..num_iters_per_step)
    //             .map(|j| MinRootIteration {
    //                 x_i: minroot_iterations[i * num_iters_per_step + j].x_i,
    //                 y_i: minroot_iterations[i * num_iters_per_step + j].y_i,
    //                 x_i_plus_1: minroot_iterations[i * num_iters_per_step + j].x_i_plus_1,
    //                 y_i_plus_1: minroot_iterations[i * num_iters_per_step + j].y_i_plus_1,
    //             })
    //             .collect::<Vec<_>>(),
    //     })
    //     .collect::<Vec<_>>();

    let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

    type C1 = Blake3BlockCompressCircuit<<E1 as Engine>::GE>;
    type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;
    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
        RecursiveSNARK::<E1, E2, C1, C2>::new(
            &pp,
            &circuit_primary,
            &circuit_secondary,
            &z0_primary,
            &z0_secondary,
        )
        .map_err(|err| {
            println!("Error: {:?}", err);
            err
        }).unwrap();

    for i in 0..N_MESSAGE_WORDS_BLOCK {
        let start = Instant::now();
        let res = recursive_snark.prove_step(&pp, &circuit_primary, &circuit_secondary);
        // Increase internal data necessary for witness generation
        circuit_primary.update_for_step();

        assert!(res.is_ok());
        println!(
            "RecursiveSNARK::prove_step {}: {:?}, took {:?} ",
            i,
            res.is_ok(),
            start.elapsed()
        );
    }

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, num_steps, &z0_primary, &z0_secondary);
    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with multilinear KZG...");
    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();

    let start = Instant::now();

    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    println!("=========================================================");
}

fn main() {}

#[cfg(test)]
mod tests {
    use crate::prove_chunk_hash;

    #[test]
    fn test_exploration() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn test_prove_chunk_hash() {
        let empty_bytes = vec![0 as u8; 1_024];
        prove_chunk_hash(empty_bytes)
    }
}
