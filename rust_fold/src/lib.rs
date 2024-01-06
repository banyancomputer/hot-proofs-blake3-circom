use arecibo::errors::NovaError;
use arecibo::provider::{PallasEngine, VestaEngine};
use arecibo::traits::circuit::TrivialCircuit;
use arecibo::traits::snark::RelaxedR1CSSNARKTrait;
use arecibo::traits::Engine;
use arecibo::CompressedSNARK;
use arecibo::PublicParams;
use arecibo::RecursiveSNARK;
use bellpepper_core::ConstraintSystem;
use blake3_circuit::PathNode;
use num_traits::ops::bytes;
use std::time::Instant;

use crate::blake3_circuit::{Blake3BlockCompressCircuit, Blake3CompressPubIO, IV};

type E1 = PallasEngine;
type E2 = VestaEngine;
type EE1 = arecibo::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

const N_MESSAGE_WORDS_BLOCK: usize = 16;
const MAX_BLOCKS_PER_CHUNK: usize = 16;
const MAX_BYTES_PER_BLOCK: usize = 64;
const MAX_BYTES_PER_CHUNK: usize = MAX_BLOCKS_PER_CHUNK * MAX_BYTES_PER_BLOCK;

mod blake3_circuit;
mod blake3_hash;
mod utils;

struct ProofResult {
    hash_out: Vec<u8>,
}

/// A PathNode contain whether or not the node is a left or right child
/// and the hash bytes

/// Using folding to prove that the prover knows all the preimages of blocks in a file
/// and that they chain together correctly.
pub fn prove_chunk_hash(
    bytes: Vec<u8>,
    chunk_idx: u64,
    parent_path: Vec<PathNode>,
) -> Result<Vec<u8>, NovaError> {
    // TODO: I think that we need to add padding stuff in somewhere (like in the circom or something?)
    println!("Nova-based Blake3 Chunk Compression");
    println!("=========================================================");

    assert!(bytes.len() <= MAX_BYTES_PER_CHUNK);

    let n_bytes = bytes.len();

    // number of iterations of MinRoot per Nova's recursive step
    let mut circuit_primary = Blake3BlockCompressCircuit::new(bytes, parent_path);
    let circuit_secondary = TrivialCircuit::default();
    println!(
        "Proving {} bytes of Blake3Compress per step",
        circuit_primary.n_bytes
    );

    // Round up to include all the blocks
    let n_blocks = circuit_primary.n_blocks;
    // We need an additional (total_depth - 1) round here (to account for all parents above the leaf)
    let num_steps = n_blocks + circuit_primary.total_depth - 1;

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

    let scalar_iv: Vec<<E1 as Engine>::Scalar> = IV
        .iter()
        .map(|iv| <E1 as Engine>::Scalar::from(*iv as u64))
        .collect();
    // TODO: I think we should move this into the blake3_circuit file
    let z0_primary = Blake3CompressPubIO::<<E1 as Engine>::GE>::new(
        <E1 as Engine>::Scalar::from(chunk_idx),
        <E1 as Engine>::Scalar::from(circuit_primary.total_depth as u64),
        <E1 as Engine>::Scalar::from(n_blocks as u64),
        scalar_iv,
    )
    .to_vec();
    println!("z0_primary len: {}", z0_primary.len());

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
        })
        .unwrap();

    // We need to do the ceiling
    for i in 0..num_steps {
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

    println!("Snark Output: {:?}", res);
    // TODO: do we return the output hash?
    assert!(res.is_ok());
    let res_un = res.unwrap().0;
    let _n_blocks = res_un[0].clone();
    let _counted_to = res_un[1].clone();
    // TODO: using formatting!!
    let output_words = res_un[2..10].to_vec();
    let output_hash = utils::format_scalar_blake_hash::<E1>(output_words.try_into().unwrap());
    println!("Output hash: {:?}", utils::format_bytes(&output_hash));

    // produce a compressed SNARK
    //    println!("Generating a CompressedSNARK using Spartan with multilinear KZG...");
    //    let (pk, vk) = CompressedSNARK::<_, _, _, _, S1, S2>::setup(&pp).unwrap();
    //
    //    let start = Instant::now();
    //
    //    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &pk, &recursive_snark);
    //    println!(
    //        "CompressedSNARK::prove: {:?}, took {:?}",
    //        res.is_ok(),
    //        start.elapsed()
    //    );
    //    assert!(res.is_ok());
    //    let compressed_snark = res.unwrap();
    //
    //    // verify the compressed SNARK
    //    println!("Verifying a CompressedSNARK...");
    //    let start = Instant::now();
    //    let res = compressed_snark.verify(&vk, num_steps, &z0_primary, &z0_secondary);
    //    println!(
    //        "CompressedSNARK::verify: {:?}, took {:?}",
    //        res.is_ok(),
    //        start.elapsed()
    //    );
    //    assert!(res.is_ok());
    //    println!("=========================================================");
    Ok(output_hash)
}

#[cfg(test)]
mod tests {
    use std::cmp::min;

    use fleek_blake3::hash;
    use num_traits::Pow;
    use rand::{rngs::StdRng, Rng, RngCore, SeedableRng};

    use crate::{
        blake3_circuit::{PathDirection, PathNode},
        blake3_hash::hash_with_path,
        prove_chunk_hash,
        utils::{self, get_depth_from_n_leaves},
        MAX_BYTES_PER_CHUNK,
    };

    // Assume that path[0] refers to the path under the root
    // And the path[depth - 1] refers to the neighbor of the leaf
    fn test_prove_path_hash(data: Vec<u8>, chunk_idx: usize) {
        let r = hash_with_path(&data, chunk_idx);
        assert!(r.is_ok());
        let (hash, path_nodes) = r.unwrap();
        print!("HASH: {:?}", hash);

        let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
        let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, data.len());

        let data = data[start_byte..end_byte].to_vec();
        let ret = prove_chunk_hash(data, chunk_idx as u64, path_nodes);
        assert!(ret.is_ok());
        let bytes = ret.unwrap();
        assert_eq!(bytes, hash.as_bytes());
    }

    fn test_prove_chunk_hash(data: Vec<u8>) {
        let r = hash_with_path(&data, 0);
        assert!(r.is_ok());

        let hash = &r.unwrap().0;
        println!("Hash: {:?}", hash);
        // TODO: remeber to check how we combine to 32 bit words vis a vis endianes
        println!("Hash bytes: {:?}", utils::format_bytes(hash.as_bytes()));
        let r = prove_chunk_hash(data, 0, vec![]);
        assert!(r.is_ok());
        let bytes = r.unwrap();
        assert_eq!(bytes, hash.as_bytes().to_vec());
    }

    // TODO: util fn to generalize
    #[test]
    fn test_random_full_bin_tree() {
        let seed = [42; 32];
        let mut rng = StdRng::from_seed(seed);
        let n_trials = 1;
        for _ in 0..n_trials {
            let n_levels = rng.gen_range(2..5);
            let n_chunks = 2u32.pow((n_levels - 1) as u32) as usize;
            let n_bytes = 1024 * (n_chunks);
            let mut bytes = vec![0 as u8; n_bytes];
            rng.fill_bytes(&mut bytes);
            let chunk_idx = rng.gen_range(0..n_chunks);
            let r = hash_with_path(&bytes, chunk_idx);
            assert!(r.is_ok());
            let (hash, path_nodes) = r.unwrap();
            print!("HASH: {:?}", hash);

            let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
            let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, bytes.len());

            let data = bytes[start_byte..end_byte].to_vec();
            let ret = prove_chunk_hash(data, chunk_idx as u64, path_nodes);
            assert!(ret.is_ok());
            let bytes = ret.unwrap();
            assert_eq!(bytes, hash.as_bytes());
        }
    }

    #[test]
    fn test_random_data_and_path() {
        // TODO:
        todo!("We need to have non full binary tree support");
        let seed = [42; 32];
        let mut rng = StdRng::from_seed(seed);
        let n_trials = 1;
        for _ in 0..n_trials {
            let n_bytes = rng.gen_range(1..(1024 * 42) + 1);
            let mut bytes = vec![0 as u8; n_bytes];
            rng.fill_bytes(&mut bytes);
            let n_chunks = (n_bytes + 1024 - 1) / 1024;
            let chunk_idx = rng.gen_range(0..n_chunks);
            let r = hash_with_path(&bytes, chunk_idx);
            assert!(r.is_ok());
            let (hash, path_nodes) = r.unwrap();
            print!("HASH: {:?}", hash);

            let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
            let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, bytes.len());

            let data = bytes[start_byte..end_byte].to_vec();
            let ret = prove_chunk_hash(data, chunk_idx as u64, path_nodes);
            assert!(ret.is_ok());
            let bytes = ret.unwrap();
            assert_eq!(bytes, hash.as_bytes());
        }
    }

    #[test]
    fn test_middle_path() {
        // We have 1 full chunk and then 4 bytes for the next byte
        let data = vec![0 as u8; 1024 * 3 + 4];
        // TODO: maybe debug_asserts throughout the code for path verif?
        // Hrmmm... maybe 
        test_prove_path_hash(data.clone(), 3);
        // 0x3c94b113d1a2f4e9b90058740c2843f45306e1dfdc3c69be25dd97cdfec89cab
        // test_prove_path_hash(data, 0);
    }

    #[test]
    fn test_simple_path() {
        // We have 1 full chunk and then 4 bytes for the next byte
        let data = vec![0 as u8; 1024 + 4];
        test_prove_path_hash(data.clone(), 1);
        // 0x3c94b113d1a2f4e9b90058740c2843f45306e1dfdc3c69be25dd97cdfec89cab
        test_prove_path_hash(data, 0);
    }

    #[test]
    fn test_random_chunk() {
        let seed = [42; 32];
        let mut rng = StdRng::from_seed(seed);

        for _ in 0..10 {
            let n_bytes = rng.gen_range(1..1025);
            let mut bytes = vec![0 as u8; n_bytes];
            rng.fill_bytes(&mut bytes);
            test_prove_chunk_hash(bytes);
        }
    }

    #[test]
    fn test_prove_chunk_hash_full_blocks() {
        // real d6fd9de5bccf223f523b316c9cd1cf9a9d87ea42473d68e011dad13f09bf8917
        // what we have 0x16fd9de5bccf223f523b316c9cd1cf9a36b41f4e2a7f6e476d060fdc09bf8914
        // Hash bytes: ["e59dfdd6", "3f22cfbc", "6c313b52", "9acfd19c", "42ea879d", "e0683d47", "3fd1da11", "1789bf09"]
        let empty_bytes = vec![0 as u8; 1_024];
        test_prove_chunk_hash(empty_bytes);
    }
    #[test]
    fn test_prove_chunk_hash_two_blocks() {
        let smallish_block = vec![0 as u8; 68];
        // Real 155e0c74d6aa369966999c8a972e3d92e6266656fd74087fa46531db452965f5
        // TODO: okay this is wrong format?
        // Hash bytes: ["740c5e15", "9936aad6", "8a9c9966", "923d2e97", "566626e6", "7f0874fd", "db3165a4", "f5652945"]
        // What we have 0x155e0c74d6aa369966999c8a972e3d92e6266656fd74087fa46531db452965f5
        test_prove_chunk_hash(smallish_block);
    }

    #[test]
    // TODO: it aint workin
    fn test_prove_chunk_hash_one_block() {
        let small_block = vec![0 as u8; 1];
        // Hash bytes: ["0xdfde3a2d", "0xf1611bf1", "0x356e884c", "0x7336a0af", "0xa787cd6d", "0xc1b5274d", "0xd0250251", "0x13e292f5"]
        test_prove_chunk_hash(small_block);
    }

    #[test]
    fn test_prove_chunk_hash_one_block_nonempty() {
        // Hash bytes: ["0x1f72fc48", "0xe072c1bb", "0x7aa25f92", "0xe21d67f1", "0x7192ba25", "0x98298034", "0x68150ab1", "0x2b6588a1"]
        let small_block = vec![117 as u8; 17];
        test_prove_chunk_hash(small_block);
    }
    // TODO: random testing inputs with seed
    // TODO: have tests verify with the actual hash!
    // OH WAIT. Do we need a root flag somewhere here?
}
