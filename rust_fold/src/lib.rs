use arecibo::provider::mlkzg::Bn256EngineKZG;
use arecibo::provider::GrumpkinEngine;
use arecibo::traits::circuit::StepCircuit;
use arecibo::traits::circuit::TrivialCircuit;
use arecibo::traits::snark::RelaxedR1CSSNARKTrait;
use arecibo::traits::Engine;
use arecibo::traits::Group;
use arecibo::CompressedSNARK;
use arecibo::PublicParams;
use arecibo::RecursiveSNARK;
use bellpepper_core::test_cs::TestConstraintSystem;
use bellpepper_core::Comparable;
use bellpepper_core::ConstraintSystem;
use circom_scotia::{calculate_witness, r1cs::CircomConfig, synthesize};
use ff::Field;
use pasta_curves::vesta::Base as Fr;
use std::env::current_dir;
use std::time::Instant;

type E1 = Bn256EngineKZG;
type E2 = GrumpkinEngine;
type EE1 = arecibo::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

const N_KEYS: usize = 8;
const N_MESSAGE_WORDS_BLOCK: usize = 16;
const MAX_BLOCKS_PER_CHUNK: usize = 16;

mod utils;

/// A single iteration of the blake3 block compression function.
/// Everything is little-endian.
#[derive(Clone, Debug)]
struct Blake3BlockCompressIteration<G: Group> {
    /// The key for this block (h_0, ..., h_7).
    keys: [G::Scalar; N_KEYS],
    /// The message set for this block (m_0, ..., m_15).
    message: [G::Scalar; N_MESSAGE_WORDS_BLOCK],
    /// Starting value for the d flag.
    d: G::Scalar,
    /// Block size
    b: G::Scalar,
}

#[derive(Clone, Debug)]
struct Blake3BlockCompressCircuit<G: Group> {
    seq: Vec<Blake3BlockCompressIteration<G>>,
}

impl<G: Group> StepCircuit<G::Scalar> for Blake3BlockCompressCircuit<G> {
    fn arity(&self) -> usize {
        // + 2 refers to the d flag and b block size
        N_KEYS + N_MESSAGE_WORDS_BLOCK + 2
    }

    fn synthesize<CS: ConstraintSystem<G::Scalar>>(
        &self,
        cs: &mut CS,
        z: &[bellpepper_core::num::AllocatedNum<G::Scalar>],
    ) -> Result<Vec<bellpepper_core::num::AllocatedNum<G::Scalar>>, bellpepper_core::SynthesisError>
    {
        let root = current_dir().unwrap().join("../circuits/compiled");
        println!("The current directory is {}", root.display());

        // TODO: make these a thing...
        // TODO: RIP. WE NEED THE WITNESS TO GENERATE AUTO-MAGICALLY HERE.
        let wtns = root.join("circom_blake3compression.wasm");
        let r1cs = root.join("circom_blake3compression.r1cs");

        let cfg = CircomConfig::<G::Scalar>::new(wtns, r1cs).unwrap();

        let arg_in = (
            "arg_in".into(),
            z.to_vec()
                .iter()
                .map(|x| x.get_value().unwrap())
                .collect::<Vec<_>>(),
        );

        let input = vec![arg_in];
        let witness = calculate_witness(&cfg, input, true).expect("msg");

        utils::synthesize_with_vec::<G::Scalar, _>(
            &mut cs.namespace(|| "blake3_circom"),
            cfg.r1cs.clone(),
            Some(witness),
            self.arity(),
        )
    }
}

/// Using folding to prove that the prover knows all the preimages of blocks in a file
/// and that they chain together correctly.
fn prove_chunk_hash() {
    println!("Nova-based Blake3 Chunk Compression");
    println!("=========================================================");

    let num_steps = N_MESSAGE_WORDS_BLOCK;
    for num_iters_per_step in [1024, 2048, 4096, 8192, 16384, 32768, 65536] {
        // number of iterations of MinRoot per Nova's recursive step
        let circuit_primary = Blake3BlockCompressCircuit {
            seq: vec![
                Blake3BlockCompressIteration {
                    keys: [<E1 as Engine>::Scalar::zero(); N_KEYS],
                    message: [<E1 as Engine>::Scalar::zero(); N_MESSAGE_WORDS_BLOCK],
                    d: <E1 as Engine>::Scalar::zero(),
                    b: <E1 as Engine>::Scalar::zero(),
                };
                num_steps
            ],
        };
        let circuit_secondary = TrivialCircuit::default();
        println!("Proving {num_iters_per_step} iterations of Blake3Compress per step");

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

        // produce non-deterministic advice
        let (z0_primary, minroot_iterations) = MinRootIteration::<<E1 as Engine>::GE>::new(
            num_iters_per_step * num_steps,
            &<E1 as Engine>::Scalar::zero(),
            &<E1 as Engine>::Scalar::one(),
        );
        let minroot_circuits = (0..num_steps)
            .map(|i| MinRootCircuit {
                seq: (0..num_iters_per_step)
                    .map(|j| MinRootIteration {
                        x_i: minroot_iterations[i * num_iters_per_step + j].x_i,
                        y_i: minroot_iterations[i * num_iters_per_step + j].y_i,
                        x_i_plus_1: minroot_iterations[i * num_iters_per_step + j].x_i_plus_1,
                        y_i_plus_1: minroot_iterations[i * num_iters_per_step + j].y_i_plus_1,
                    })
                    .collect::<Vec<_>>(),
            })
            .collect::<Vec<_>>();

        let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

        type C1 = MinRootCircuit<<E1 as Engine>::GE>;
        type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;
        // produce a recursive SNARK
        println!("Generating a RecursiveSNARK...");
        let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
            RecursiveSNARK::<E1, E2, C1, C2>::new(
                &pp,
                &minroot_circuits[0],
                &circuit_secondary,
                &z0_primary,
                &z0_secondary,
            )
            .unwrap();

        for (i, circuit_primary) in minroot_circuits.iter().enumerate() {
            let start = Instant::now();
            let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
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

        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        bincode::serialize_into(&mut encoder, &compressed_snark).unwrap();
        let compressed_snark_encoded = encoder.finish().unwrap();
        println!(
            "CompressedSNARK::len {:?} bytes",
            compressed_snark_encoded.len()
        );

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

        todo!()
    }
}

fn main() {
    let root = current_dir().unwrap().join("examples/sha256");
    println!("The current directory is {}", root.display());

    let wtns = root.join("circom_sha256.wasm");
    let r1cs = root.join("circom_sha256.r1cs");

    let mut cs = TestConstraintSystem::<Fr>::new();
    let cfg = CircomConfig::new(wtns, r1cs).unwrap();

    let arg_in = ("arg_in".into(), vec![Fr::ZERO, Fr::ZERO]);
    let input = vec![arg_in];
    let witness = calculate_witness(&cfg, input, true).expect("msg");

    let output = synthesize(
        &mut cs.namespace(|| "sha256_circom"),
        cfg.r1cs.clone(),
        Some(witness),
    );

    let expected = "0x00000000008619b3767c057fdf8e6d99fde2680c5d8517eb06761c0878d40c40";
    let output_num = format!("{:?}", output.unwrap().get_value().unwrap());
    assert!(output_num == expected);

    assert!(cs.is_satisfied());
    assert_eq!(30134, cs.num_constraints());
    assert_eq!(1, cs.num_inputs());
    assert_eq!(29822, cs.aux().len());

    println!("Congrats! You synthesized and satisfied a circom sha256 circuit in bellpepper!");
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_exploration() {
        assert_eq!(2 + 2, 4);
    }
}
