use arecibo::traits::circuit::StepCircuit;
use arecibo::traits::Group;
use bellpepper_core::num::AllocatedNum;
use bellpepper_core::ConstraintSystem;
use circom_scotia::{calculate_witness, r1cs::CircomConfig};
use ff::Field;
use std::str::FromStr;
use std::{cmp::min, path::PathBuf};

use crate::utils::{self, pad_vector_to_min_length};

const N_KEYS: usize = 8;
const MAX_BYTES_PER_BLOCK: usize = 64;

const IO_ARITY: usize = 15;

pub const IV: [u32; N_KEYS] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

// TODO: we should make this for **private** and **public** inputs
// so then we have a bit of an easier time later when we move as much as possible (provably)
// to private inputs
pub struct Blake3CompressPubIO<G: Group> {
    chunk_idx_low: G::Scalar,
    chunk_idx_high: G::Scalar,
    depth: G::Scalar,
    total_depth: G::Scalar,
    n_blocks: G::Scalar,
    block_count: G::Scalar,
    h_keys: [G::Scalar; 8],
    leaf_depth: G::Scalar,
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
pub struct PathNode(PathDirection, [u8; 32]);

impl PathNode {
    pub fn new(path_dir: PathDirection, hash: [u8; 32]) -> Self {
        PathNode(path_dir, hash)
    }
}

#[derive(Debug, Clone)]
pub struct Blake3BlockCompressCircuit<G: Group> {
    leaf_bytes: Vec<u8>,
    pub(crate) n_bytes: usize,
    pub(crate) total_depth: usize,
    pub(crate) n_blocks: usize,
    current_depth: usize,
    current_block: usize,
    parent_path: Vec<PathNode>,
    circom_path_wasm: String,
    circom_path_r1cs: String,
    // TODO:
    // cfg: CircomConfig<G::Scalar>,
    _p: std::marker::PhantomData<G>,
}

fn load_cfg<G: Group>(wtns: &str, r1cs: &str) -> CircomConfig<G::Scalar> {
    // Load the R1CS
    // TODO: instead of unwrap, return error?
    let cfg = CircomConfig::<G::Scalar>::new(
        PathBuf::from_str(wtns).unwrap(),
        PathBuf::from_str(r1cs).unwrap(),
    )
    .unwrap();
    println!("Loaded config for R1CS");
    cfg
}

impl<G: Group> Blake3CompressPubIO<G> {
    pub(crate) fn new(
        chunk_idx: u64,
        total_depth: G::Scalar,
        n_blocks: G::Scalar,
        h_keys: Vec<G::Scalar>,
        leaf_depth: G::Scalar,
    ) -> Self {
        assert!(h_keys.len() == 8);
        let high = (chunk_idx >> 32) as u32;
        let low = chunk_idx as u32;

        let mut h = [G::Scalar::ZERO; 8];
        h.copy_from_slice(&h_keys[..8]);
        let depth = total_depth - G::Scalar::ONE;
        Blake3CompressPubIO {
            chunk_idx_low: G::Scalar::from(low as u64),
            chunk_idx_high: G::Scalar::from(high as u64),
            total_depth,
            depth,
            n_blocks,
            block_count: G::Scalar::from(0),
            h_keys: h,
            leaf_depth,
        }
    }

    pub(crate) fn to_vec(&self) -> Vec<G::Scalar> {
        let mut vec = Vec::new();
        vec.push(self.n_blocks);
        vec.push(self.block_count);
        vec.extend_from_slice(&self.h_keys);
        vec.push(self.total_depth);
        vec.push(self.depth);
        vec.push(self.chunk_idx_low);
        vec.push(self.chunk_idx_high);
        vec.push(self.leaf_depth);
        assert!(vec.len() == IO_ARITY);
        vec
    }

    fn from_vec(vec: Vec<G::Scalar>) -> Blake3CompressPubIO<G> {
        assert!(vec.len() == IO_ARITY);
        let n_blocks = vec[0];
        let block_count = vec[1];
        let h = [
            vec[2], vec[3], vec[4], vec[5], vec[6], vec[7], vec[8], vec[9],
        ];
        let total_depth = vec[10];
        let depth = vec[11];
        let chunk_idx_low = vec[12];
        let chunk_idx_high = vec[13];
        let leaf_depth = vec[14];
        Blake3CompressPubIO {
            total_depth,
            depth,
            n_blocks,
            block_count,
            h_keys: h,
            chunk_idx_low,
            chunk_idx_high,
            leaf_depth,
        }
    }

    fn from_alloced_vec(vec: Vec<AllocatedNum<G::Scalar>>) -> Blake3CompressPubIO<G> {
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
    pub fn new(
        bytes: Vec<u8>,
        parent_path: Vec<PathNode>,
        circom_path_wasm: String,
        circom_path_r1cs: String,
    ) -> Blake3BlockCompressCircuit<G> {
        let bytes_len = bytes.len();
        let n_blocks = utils::n_blocks_from_bytes(bytes_len);
        let depth = parent_path.len() + 1;

        Blake3BlockCompressCircuit {
            n_bytes: bytes_len,
            n_blocks,
            leaf_bytes: bytes,
            parent_path,
            current_block: 0,
            total_depth: depth,
            current_depth: depth - 1,
            circom_path_r1cs,
            circom_path_wasm,
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
        let io_input = Blake3CompressPubIO::<G>::from_alloced_vec(z.to_vec());

        let not_parent = self.current_block < self.n_blocks;
        let (message_block_scalar, b) = if not_parent {
            println!("Doing leaf");
            // 4 bytes per 32-bit word
            let start_idx = self.current_block * 4 * 16;
            let end_idx = min(start_idx + 4 * 16, self.n_bytes);

            let mut message_bytes = self.leaf_bytes[start_idx..end_idx].to_vec();
            // The number of 32 bit words (4 byte) in the message
            pad_vector_to_min_length(&mut message_bytes, MAX_BYTES_PER_BLOCK, 0);
            let as_u32 = utils::bytes_to_u32_le(&message_bytes);
            let n_bytes_per_block = (end_idx - start_idx) as u64;
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
            let b = G::Scalar::from(64u64);
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
            let empty = vec![G::Scalar::ZERO; 8];
            m.extend_from_slice(&empty);
            println!("Sib value {:?} {:?}", message_bytes, path_node.0);
            println!("chaining value: {:?}", io_input.h_keys);
            (m, b)
        };

        println!(
            "DEPTH {:?}, total depth {:?}. chunk idx  {:?} :: {:?}. LEAF TOTAL DEPTH {:?}",
            io_input.depth, io_input.total_depth, io_input.chunk_idx_low, io_input.chunk_idx_high,
            io_input.leaf_depth
        );

        let b_arg = ("b".to_string(), vec![b]);
        let msg_arg = ("m".into(), message_block_scalar);
        // I GOT YOU BUGGER!
        // This is *different* for parent values vs. not
        // TODO: does this always have to be I/O based?
        let override_h_to_iv_val = if not_parent {
            <G as Group>::Scalar::ZERO
        } else {
            <G as Group>::Scalar::ONE
        };
        let override_h_to_iv = ("override_h_to_IV".into(), vec![override_h_to_iv_val]);
        let key_args = ("h".into(), io_input.h_keys.to_vec());
        let current_block_arg = ("block_count".into(), vec![io_input.block_count]);
        let n_block_args = ("n_blocks".into(), vec![io_input.n_blocks]);
        let total_depth = ("total_depth".into(), vec![io_input.total_depth]);
        let depth = ("depth".into(), vec![io_input.depth]);
        let chunk_idx_low = ("chunk_idx_low".into(), vec![io_input.chunk_idx_low]);
        let chunk_idx_high = ("chunk_idx_high".into(), vec![io_input.chunk_idx_high]);
        let leaf_depth = ("leaf_depth".into(), vec![io_input.leaf_depth]);

        let input = vec![
            b_arg,
            msg_arg,
            chunk_idx_low,
            chunk_idx_high,
            key_args,
            current_block_arg,
            n_block_args,
            total_depth,
            depth,
            override_h_to_iv,
            leaf_depth,
        ];
        Ok(input)
    }
}

impl<G: Group> StepCircuit<G::Scalar> for Blake3BlockCompressCircuit<G> {
    fn arity(&self) -> usize {
        IO_ARITY
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<G::Scalar>>, bellpepper_core::SynthesisError>
    {
        let cfg = load_cfg::<G>(&self.circom_path_wasm, &self.circom_path_r1cs);
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
