use arecibo::errors::NovaError;
use arecibo::provider::non_hiding_zeromorph::ZMPCS;
use arecibo::provider::{
    self, Bn256Engine, Bn256EngineZM, GrumpkinEngine, PallasEngine, VestaEngine,
};
use arecibo::traits::circuit::TrivialCircuit;
use arecibo::traits::snark::RelaxedR1CSSNARKTrait;
use arecibo::traits::Engine;
use arecibo::RecursiveSNARK;
use arecibo::{spartan, PublicParams};
use arecibo::{CompressedSNARK, ProverKey, VerifierKey};
use bellpepper_core::ConstraintSystem;
use blake3_circuit::PathNode;
use ff::Field;
use halo2curves::bn256::Bn256;
use num_traits::ops::bytes;
use std::fs;
use std::marker::PhantomData;
use std::time::Instant;

use crate::blake3_circuit::{Blake3BlockCompressCircuit, Blake3CompressPubIO, IV};
use crate::blake3_hash::hash_with_path;

const N_MESSAGE_WORDS_BLOCK: usize = 16;
const MAX_BLOCKS_PER_CHUNK: usize = 16;
const MAX_BYTES_PER_BLOCK: usize = 64;
const MAX_BYTES_PER_CHUNK: usize = MAX_BLOCKS_PER_CHUNK * MAX_BYTES_PER_BLOCK;

const DEFAULT_CIRCOM_WASM_PATH: &str = "../build/blake3_nova_js/blake3_nova.wasm";
const DEFAULT_CIRCOM_R1CS_PATH: &str = "../build/blake3_nova.r1cs";

mod blake3_circuit;
mod blake3_hash;
mod utils;

/// A PathNode contain whether or not the node is a left or right child
/// and the hash bytes

/// Using folding to prove that the prover knows all the preimages of blocks in a file
/// and that they chain together correctly.
pub fn prove_chunk_hash<E1, E2, SS1, SS2>(
    hash_proof: blake3_hash::Blake3HashProof,
    circom_wasm_path: Option<String>,
    circom_r1cs_path: Option<String>,
) -> Result<
    (
        Vec<u8>,
        PublicParams<
            E1,
            E2,
            Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
        >,
        RecursiveSNARK<
            E1,
            E2,
            Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
            TrivialCircuit<<E2 as Engine>::Scalar>,
        >,
    ),
    NovaError,
>
where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    SS1: RelaxedR1CSSNARKTrait<E1>,
    SS2: RelaxedR1CSSNARKTrait<E2>,
{
    // TODO: I think that we need to add padding stuff in somewhere (like in the circom or something?)
    println!("Nova-based Blake3 Chunk Compression");
    println!("=========================================================");
    let leaf_depth = hash_proof.parent_path.len() as u64 + 1;
    let bytes = hash_proof.bytes;
    let chunk_idx = hash_proof.chunk_idx;
    let parent_path = hash_proof.parent_path;

    assert!(bytes.len() <= MAX_BYTES_PER_CHUNK);

    // number of iterations of MinRoot per Nova's recursive step
    let mut circuit_primary = Blake3BlockCompressCircuit::new(
        bytes,
        parent_path,
        circom_wasm_path.unwrap_or(DEFAULT_CIRCOM_WASM_PATH.into()),
        circom_r1cs_path.unwrap_or(DEFAULT_CIRCOM_WASM_PATH.into()),
    );
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
        &*SS1::ck_floor(),
        &*SS2::ck_floor(),
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
        chunk_idx,
        <E1 as Engine>::Scalar::from(circuit_primary.total_depth as u64),
        <E1 as Engine>::Scalar::from(n_blocks as u64),
        scalar_iv,
        <E1 as Engine>::Scalar::from(leaf_depth),
    )
    .to_vec();
    println!("z0_primary len: {}", z0_primary.len());

    let z0_secondary = vec![<E2 as Engine>::Scalar::ZERO];

    type C1<E1> = Blake3BlockCompressCircuit<<E1 as Engine>::GE>;
    type C2<E2> = TrivialCircuit<<E2 as Engine>::Scalar>;
    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK...");
    let mut recursive_snark: RecursiveSNARK<E1, E2, C1<E1>, C2<E2>> =
        RecursiveSNARK::<E1, E2, C1<E1>, C2<E2>>::new(
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
    let output_hash =
        utils::format_scalar_blake_hash::<<E1 as Engine>::GE>(output_words.try_into().unwrap());
    println!("Output hash: {:?}", utils::format_bytes(&output_hash));

    Ok((output_hash, pp, recursive_snark))
}

fn get_compressed_snark_keys<E1, E2, SS1, SS2>() -> (
    arecibo::ProverKey<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
        SS1,
        SS2,
    >,
    arecibo::VerifierKey<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
        SS1,
        SS2,
    >,
)
where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    SS1: RelaxedR1CSSNARKTrait<E1>,
    SS2: RelaxedR1CSSNARKTrait<E2>,
{
    // These input params do not influence the verifier key
    // TODO: verify ^^
    // TODO: DO IT MATTER?
    let circuit_primary = Blake3BlockCompressCircuit::new(
        vec![0u8; 1],
        vec![],
        DEFAULT_CIRCOM_WASM_PATH.to_string(),
        DEFAULT_CIRCOM_R1CS_PATH.to_string(),
    );
    let circuit_secondary = TrivialCircuit::default();
    println!(
        "Proving {} bytes of Blake3Compress per step",
        circuit_primary.n_bytes
    );

    // produce public parameters
    let pp = PublicParams::<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
    >::setup(
        &circuit_primary,
        &circuit_secondary,
        &*SS1::ck_floor(),
        &*SS2::ck_floor(),
    );
    let (pk, vk) = CompressedSNARK::<_, _, _, _, SS1, SS2>::setup(&pp).unwrap();
    (pk, vk)
}

pub fn compress_snark<E1, E2, SS1, SS2>(
    pp: &PublicParams<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
    >,
    pk: &ProverKey<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
        SS1,
        SS2,
    >,
    vk: &VerifierKey<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
        SS1,
        SS2,
    >,
    recursive_snark: &RecursiveSNARK<
        E1,
        E2,
        Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
        TrivialCircuit<<E2 as Engine>::Scalar>,
    >,
) -> CompressedSNARK<
    E1,
    E2,
    Blake3BlockCompressCircuit<<E1 as Engine>::GE>,
    TrivialCircuit<<E2 as Engine>::Scalar>,
    SS1,
    SS2,
>
where
    E1: Engine<Base = <E2 as Engine>::Scalar>,
    E2: Engine<Base = <E1 as Engine>::Scalar>,
    SS1: RelaxedR1CSSNARKTrait<E1>,
    SS2: RelaxedR1CSSNARKTrait<E2>,
{
    // let (pk, vk) = get_compressed_snark_keys();
    let start = Instant::now();

    let res = CompressedSNARK::<_, _, _, _, SS1, SS2>::prove(&pp, &pk, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();
    compressed_snark
}

// TODO: cli
pub fn main() {
    // type NE = Engine<GE = E1::G1, Scalar = E1::Fr>;
    type E1 = Bn256EngineZM;
    type E2 = GrumpkinEngine;
    type EE1 = ZMPCS<Bn256, Bn256EngineZM>;
    // arecibo::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
    // type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
    // type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

    type SPrime<E, EE> = spartan::ppsnark::RelaxedR1CSSNARK<E, EE>;
    type SS1 = SPrime<E1, EE1>;
    // ZMPCS<Bn256, EE1>;
    // type SS1 = arecibo::spartan::ppsnark::RelaxedR1CSSNARK<E1, EE1>;
    type SS2 = SPrime<E2, EE2>; //arecibo::spartan::ppsnark::RelaxedR1CSSNARK<E2, EE2>;

    let (pk, vk) = get_compressed_snark_keys::<E1, E2, SS1, SS2>();
    let s = serde_json::to_string(&vk).unwrap();
    let s_pk = serde_json::to_string(&pk).unwrap();
    // TODO: arg for path...
    fs::write("../../solidity-verifier/vk_zm.json", s).expect("Unable to write file");
    let hash_proof = hash_with_path(&vec![0u8], 0).unwrap();
    let (_, pp, rec_s) = prove_chunk_hash::<E1, E2, SS1, SS2>(hash_proof.1, None, None).unwrap();
    println!("Compressing");
    let compr_snark = compress_snark(&pp, &pk, &vk, &rec_s);
    fs::write(
        "../../solidity-verifier/proof.json",
        serde_json::to_string(&compr_snark).unwrap(),
    )
    .expect("Unable to write file");

    // fs::write("../../solidity-verifier/pk.json", s_pk).expect("Unable to write file");
}

#[cfg(test)]
mod tests {
    use std::cmp::min;

    use arecibo::provider::{PallasEngine, VestaEngine};
    use ff::derive::bitvec::vec;
    use num_traits::Pow;
    use rand::{rngs::StdRng, Rng, RngCore, SeedableRng};

    use crate::{
        blake3_circuit::{PathDirection, PathNode},
        blake3_hash::hash_with_path,
        compress_snark, get_compressed_snark_keys, prove_chunk_hash,
        utils::{self, get_depth_from_n_leaves},
        MAX_BYTES_PER_CHUNK,
    };

    const PASTA_CIRCOM_WASM_PATH: &str = "../build/blake3_nova_pasta_js/blake3_nova_pasta.wasm";
    const PASTA_CIRCOM_R1CS_PATH: &str = "../build/blake3_nova_pasta.r1cs";
    type E1 = PallasEngine;
    type E2 = VestaEngine;
    type EE1 = arecibo::provider::ipa_pc::EvaluationEngine<E1>;
    type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
    type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
    type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

    // Assume that path[0] refers to the path under the root
    // And the path[depth - 1] refers to the neighbor of the leaf
    fn test_prove_path_hash(data: Vec<u8>, chunk_idx: usize) {
        let r = hash_with_path(&data, chunk_idx);
        assert!(r.is_ok());
        let (hash, hash_proof) = r.unwrap();
        print!("HASH: {:?}", hash);

        let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
        let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, data.len());

        let data = data[start_byte..end_byte].to_vec();
        let ret = prove_chunk_hash::<E1, E2, S1, S2>(
            hash_proof,
            Some(PASTA_CIRCOM_WASM_PATH.to_string()),
            Some(PASTA_CIRCOM_R1CS_PATH.to_string()),
        );
        assert!(ret.is_ok());
        let bytes = ret.unwrap().0;
        assert_eq!(bytes, hash.as_bytes());
    }

    fn test_prove_chunk_hash(data: Vec<u8>) {
        let r = hash_with_path(&data, 0);
        assert!(r.is_ok());

        let rr = r.unwrap();
        let hash = &rr.0;
        println!("Hash: {:?}", hash);
        // TODO: remeber to check how we combine to 32 bit words vis a vis endianes
        println!("Hash bytes: {:?}", utils::format_bytes(hash.as_bytes()));
        let r = prove_chunk_hash::<E1, E2, S1, S2>(
            rr.1,
            Some(PASTA_CIRCOM_WASM_PATH.to_string()),
            Some(PASTA_CIRCOM_R1CS_PATH.to_string()),
        );
        assert!(r.is_ok());
        let bytes = r.unwrap().0;
        assert_eq!(bytes, hash.as_bytes().to_vec());
    }

    // TODO: util fn to generalize
    #[test]
    fn test_random_bin_tree() {
        let seed = [42; 32];
        let mut rng = StdRng::from_seed(seed);
        let n_trials = 10;
        for _ in 0..n_trials {
            let n_chunks = rng.gen_range(2..128);
            let n_bytes = 1024 * (n_chunks);
            let mut bytes = vec![0 as u8; n_bytes];
            rng.fill_bytes(&mut bytes);
            let chunk_idx = rng.gen_range(0..n_chunks);
            println!("Chunk idx: {}", chunk_idx);
            let r = hash_with_path(&bytes, chunk_idx);
            assert!(r.is_ok());
            let (hash, hash_proof) = r.unwrap();
            print!("HASH: {:?}", hash);

            let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
            let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, bytes.len());

            let data = bytes[start_byte..end_byte].to_vec();
            let ret = prove_chunk_hash::<E1, E2, S1, S2>(
                hash_proof,
                Some(PASTA_CIRCOM_WASM_PATH.to_string()),
                Some(PASTA_CIRCOM_R1CS_PATH.to_string()),
            );
            assert!(ret.is_ok());
            let bytes = ret.unwrap().0;
            assert_eq!(bytes, hash.as_bytes().to_vec());
        }
    }

    // TODO: util fn to generalize
    #[test]
    fn test_random_full_bin_tree() {
        let seed = [42; 32];
        let mut rng = StdRng::from_seed(seed);
        let n_trials = 10;
        for _ in 0..n_trials {
            let n_levels = rng.gen_range(2..5);
            let n_chunks = 2u32.pow((n_levels - 1) as u32) as usize;
            let n_bytes = 1024 * (n_chunks);
            let mut bytes = vec![0 as u8; n_bytes];
            rng.fill_bytes(&mut bytes);
            let chunk_idx = rng.gen_range(0..n_chunks);
            println!("Chunk idx: {}", chunk_idx);
            let r = hash_with_path(&bytes, chunk_idx);
            assert!(r.is_ok());
            let (hash, hash_proof) = r.unwrap();
            print!("HASH: {:?}", hash);

            let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
            let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, bytes.len());

            let data = bytes[start_byte..end_byte].to_vec();
            let ret = prove_chunk_hash::<E1, E2, S1, S2>(
                hash_proof,
                Some(PASTA_CIRCOM_WASM_PATH.to_string()),
                Some(PASTA_CIRCOM_R1CS_PATH.to_string()),
            );
            assert!(ret.is_ok());
            let bytes = ret.unwrap().0;
            assert_eq!(bytes, hash.as_bytes().to_vec());
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
            let (hash, hash_proof) = r.unwrap();
            print!("HASH: {:?}", hash);

            let start_byte = chunk_idx * MAX_BYTES_PER_CHUNK;
            let end_byte = min(start_byte + MAX_BYTES_PER_CHUNK, bytes.len());

            let data = bytes[start_byte..end_byte].to_vec();
            let ret = prove_chunk_hash::<E1, E2, S1, S2>(
                hash_proof,
                Some(PASTA_CIRCOM_WASM_PATH.to_string()),
                Some(PASTA_CIRCOM_R1CS_PATH.to_string()),
            );
            assert!(ret.is_ok());
            let bytes = ret.unwrap().0;
            assert_eq!(bytes, hash.as_bytes());
        }
    }

    #[test]
    fn test_middle_path() {
        // We have 1 full chunk and then 4 bytes for the next byte
        let data = vec![0 as u8; 1024 * 3 + 5];
        // TODO: maybe debug_asserts throughout the code for path verif?
        // Hrmmm... maybe
        test_prove_path_hash(data.clone(), 2);
        test_prove_path_hash(data.clone(), 3);
        // 0x3c94b113d1a2f4e9b90058740c2843f45306e1dfdc3c69be25dd97cdfec89cab
        // test_prove_path_hash(data, 0);
    }

    #[test]
    fn test_simple_path() {
        // We have 1 full chunk and then 4 bytes for the next byte
        let data = vec![0 as u8; 1024 + 4];
        // Okay error not in m, not in Flag setting
        test_prove_path_hash(data.clone(), 1);
        test_prove_path_hash(data.clone(), 0);
        // 0x3c94b113d1a2f4e9b90058740c2843f45306e1dfdc3c69be25dd97cdfec89cab
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
        let small_block = vec![0 as u8; 4];
        // Hash bytes: ["0xdfde3a2d", "0xf1611bf1", "0x356e884c", "0x7336a0af", "0xa787cd6d", "0xc1b5274d", "0xd0250251", "0x13e292f5"]
        test_prove_chunk_hash(small_block);
    }

    #[test]
    fn test_prove_chunk_hash_one_block_nonempty() {
        // Hash bytes: ["0x1f72fc48", "0xe072c1bb", "0x7aa25f92", "0xe21d67f1", "0x7192ba25", "0x98298034", "0x68150ab1", "0x2b6588a1"]
        let small_block = vec![117 as u8; 17];
        test_prove_chunk_hash(small_block);
    }

    #[test]
    fn test_compress() {
        // TODO: test compress v nice
        // let data = vec![0 as u8; 1];
        // let r = hash_with_path(&data, 0);
        // assert!(r.is_ok());

        // let rr = r.unwrap();
        // let hash = &rr.0;
        // println!("Hash: {:?}", hash);
        // println!("Hash bytes: {:?}", utils::format_bytes(hash.as_bytes()));
        // let r = prove_chunk_hash(rr.1);
        // assert!(r.is_ok());
        // let (_, pp, c) = r.unwrap();
        // let (pk, vk) = get_compressed_snark_keys();
        // let cp = compress_snark(&pp, &pk, &vk, &c);

        // cp.verify(&vk, num_steps, z0_primary, z0_secondary)
    }
    // TODO: random testing inputs with seed
    // TODO: have tests verify with the actual hash!
    // OH WAIT. Do we need a root flag somewhere here?
}
