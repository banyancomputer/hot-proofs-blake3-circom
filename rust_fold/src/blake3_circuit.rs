use arecibo::provider::{PallasEngine, VestaEngine};
use arecibo::traits::circuit::StepCircuit;
use arecibo::traits::Group;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;
use circom_scotia::{calculate_witness, r1cs::CircomConfig};
use ff::Field;
use std::cmp::min;
use std::env::current_dir;

use crate::utils::{self, get_depth_from_n_leaves, pad_vector_to_min_length};

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

pub const IV: [u32; N_KEYS] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

pub struct Blake3CompressPubIO<G: Group> {
    depth: G::Scalar,
    total_depth: G::Scalar,
    n_blocks: G::Scalar,
    block_count: G::Scalar,
    h_keys: [G::Scalar; 8],
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PathDirection {
    Left,
    Right,
}

#[derive(Debug, Clone)]
/// PathDirection here indicates which direction the node descends towards the leaf
/// (i.e. left or right)
/// The hash of [u8; 32] is the hash of the other child node which is not descended to
/// So, if we descend to the left, the hash is the right child node
/// If we descend to the right, the hash is the left child node
pub(crate) struct PathNode(PathDirection, [u8; 32]);

impl PathNode {
    pub fn new(path_dir: PathDirection, hash: [u8; 32]) -> Self {
        PathNode(path_dir, hash)
    }
}

#[derive(Debug, Clone)]
pub struct Blake3BlockCompressCircuit<G: Group> {
    leaf_bytes: Vec<u8>,
    // TODO: update circom accordingly
    pub(crate) n_bytes: usize,
    pub(crate) total_depth: usize,
    pub(crate) n_blocks: usize,
    current_depth: usize,
    current_block: usize,
    parent_path: Vec<PathNode>,
    _p: std::marker::PhantomData<G>,
}

fn load_cfg<G: Group>() -> CircomConfig<G::Scalar> {
    // Load the R1CS
    let root = current_dir().unwrap().join("../build/");
    println!("The current directory is {}", root.display());
    // TODO: make these a thing...
    // TODO: RIP. WE NEED THE WITNESS TO GENERATE AUTO-MAGICALLY HERE.
    // TODO: maybe this should be within new? Like why remake it with each synthesize?
    let wtns = root.join("blake3_nova_js/blake3_nova.wasm");
    let r1cs = root.join("blake3_nova.r1cs");
    let cfg = CircomConfig::<G::Scalar>::new(wtns, r1cs).unwrap();
    println!("Loaded config for R1CS");
    cfg
}

impl<G: Group> Blake3CompressPubIO<G> {
    pub(crate) fn new(total_depth: G::Scalar, n_blocks: G::Scalar, h_keys: Vec<G::Scalar>) -> Self {
        assert!(h_keys.len() == 8);
        let mut h = [G::Scalar::ZERO; 8];
        h.copy_from_slice(&h_keys[..8]);
        let depth = total_depth - G::Scalar::ONE;
        Blake3CompressPubIO {
            total_depth,
            depth,
            n_blocks,
            block_count: G::Scalar::from(0),
            h_keys: h,
        }
    }

    pub(crate) fn to_vec(&self) -> Vec<G::Scalar> {
        let mut vec = Vec::new();
        vec.push(self.n_blocks);
        vec.push(self.block_count);
        vec.extend_from_slice(&self.h_keys);
        vec.push(self.total_depth);
        vec.push(self.depth);
        assert!(vec.len() == 12);
        vec
    }

    fn from_vec(vec: Vec<G::Scalar>) -> Blake3CompressPubIO<G> {
        // TODO: flexible? nah we good
        assert!(vec.len() == 12);
        let n_blocks = vec[0];
        let block_count = vec[1];
        let h = [
            vec[2], vec[3], vec[4], vec[5], vec[6], vec[7], vec[8], vec[9],
        ];
        let total_depth = vec[10];
        let depth = vec[11];
        Blake3CompressPubIO {
            total_depth,
            depth,
            n_blocks,
            block_count,
            h_keys: h,
        }
    }

    fn from_alloced_vec(vec: Vec<AllocatedNum<G::Scalar>>) -> Blake3CompressPubIO<G> {
        // assert!(vec.len() == 10);
        // We unwrap here for "shape" testing purposed within Nova. (I.e. determining number of constraints, etc
        // When running the actual circuit, we will not unwrap here.
        let vals: Vec<G::Scalar> = vec
            .iter()
            .map(|x| x.get_value().unwrap_or_else(|| G::Scalar::ZERO))
            .collect();
        Self::from_vec(vals)
    }
}

impl<G: Group> Blake3BlockCompressCircuit<G> {
    pub fn new(bytes: Vec<u8>, parent_path: Vec<PathNode>) -> Blake3BlockCompressCircuit<G> {
        // TODO: ceiling
        // We need to check that the ceiling of the bytes split up into 4-byte words
        // is less than or equal to the max number of blocks per chunk.
        // assert!(
        //     bytes.len() <= MAX_BYTES_PER_BLOCK * MAX_BLOCKS_PER_CHUNK,
        //     "Too many bytes per chunk"
        // );

        let bytes_len = bytes.len();
        let n_blocks = utils::n_blocks_from_bytes(bytes_len);

        // assert_eq!(
        //     parent_path.len() + 1,
        //     expected_depth,
        //     "Parent path is not the correct length"
        // );

        let depth = parent_path.len() + 1;

        Blake3BlockCompressCircuit {
            n_bytes: bytes_len,
            n_blocks,
            leaf_bytes: bytes,
            parent_path,
            // TODO: it aint actually chunk len
            current_block: 0,
            total_depth: depth,
            current_depth: depth - 1,
            _p: std::marker::PhantomData,
        }
    }

    pub fn update_for_step(&mut self) -> () {
        // If we are still absorbing the input
        if self.current_block < self.n_blocks {
            self.current_block += 1;
        }
        // We start updating for the parent path when we finish absorbing all the blocks
        // Note that this can happen after updating self.n_blocks
        if self.current_block == self.n_blocks && self.current_depth > 0 {
            self.current_depth -= 1;
        }
    }

    fn format_input(
        &self,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<(String, Vec<G::Scalar>)>, bellpepper_core::SynthesisError> {
        // TODO: formailize mapping?

        let input_pub = Blake3CompressPubIO::<G>::from_alloced_vec(z.to_vec());

        let (message_block_scalar, b) = if self.current_block < self.n_blocks {
            println!("Doing leaf");
            // 4 bytes per 32-bit word
            let start_idx = self.current_block * 4 * 16;
            println!(
                "Start idx: {} and current block: {}",
                start_idx, self.current_block
            );
            let end_idx = min(start_idx + 4 * 16, self.n_bytes);

            let mut message_bytes = self.leaf_bytes[start_idx..end_idx].to_vec();
            // The number of 32 bit words (4 byte) in the message
            pad_vector_to_min_length(&mut message_bytes, MAX_BYTES_PER_BLOCK, 0);
            let as_u32 = utils::bytes_to_u32_le(&message_bytes);
            let n_bytes_per_block = (end_idx - start_idx) as u64;
            println!(
                "n_bytes: {}. Start: {}, End: {}",
                n_bytes_per_block, start_idx, end_idx
            );
            assert!(
                n_bytes_per_block <= MAX_BYTES_PER_BLOCK as u64,
                "Too many bytes per block"
            );
            // The number of bytes
            let b = G::Scalar::from(n_bytes_per_block);

            (
                as_u32.iter().map(|x| G::Scalar::from(*x as u64)).collect(),
                b,
            )
        } else {
            println!("Doing alternative");
            // We always have b=64 for a parent block
            let b = G::Scalar::from(64);
            // Note that parent_path.len() = total_depth - 1. As we never access
            // parent_path at the leaf processing, we do not access parent_path[total_depth - 1] (illegal)
            let path_node = &self.parent_path[self.current_depth];
            let message_bytes = path_node.1;
            // TODO: IDK. Little endian everything...
            // We need to work with everything in little endian from the beginning
            let as_u32 = utils::bytes_to_u32_le(&message_bytes);
            assert!(as_u32.len() == 8);
            let mut m = as_u32
                .iter()
                .map(|x| G::Scalar::from(*x as u64))
                .collect::<Vec<G::Scalar>>();

            println!("Sib value {:?} {:?}", message_bytes, path_node.0);
            println!("chaining value: {:?}", input_pub.h_keys);
            // We add a left neighboring child when descending right
            if path_node.0 == PathDirection::Right {
                m.extend_from_slice(&input_pub.h_keys);
                (m, b)
            } else {
                // TODO: there has to be a better way of doing this
                let mut m_c = input_pub.h_keys.to_vec();
                m_c.extend_from_slice(&m);
                (m_c, b)
            }
        };

        println!("z boys: {}", z.len());
        println!(
            "DEPTH {:?}, total depth {:?}. N_blocks {:?}, curr block {:?}",
            input_pub.depth, input_pub.total_depth, input_pub.n_blocks, input_pub.block_count
        );

        let b_arg = ("b".to_string(), vec![b]);
        let msg_arg = ("m".into(), message_block_scalar);
        let key_args = ("h".into(), input_pub.h_keys.to_vec());
        let current_block_arg = ("block_count".into(), vec![input_pub.block_count]);
        let n_block_args = ("n_blocks".into(), vec![input_pub.n_blocks]);
        let total_depth = ("total_depth".into(), vec![input_pub.total_depth]);
        let depth = ("depth".into(), vec![input_pub.depth]);

        let input = vec![
            b_arg,
            msg_arg,
            key_args,
            current_block_arg,
            n_block_args,
            total_depth,
            depth,
        ];
        Ok(input)
    }
}

impl<G: Group> StepCircuit<G::Scalar> for Blake3BlockCompressCircuit<G> {
    fn arity(&self) -> usize {
        //  TODO: docs
        // TODO: IDK
        // TODO: maybe we a default in IO args...
        N_KEYS + 4
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<G::Scalar>>, bellpepper_core::SynthesisError>
    {
        //  TODO: this should be dummy-loading
        let cfg = load_cfg::<G>();
        let input = self.format_input(z)?;
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
