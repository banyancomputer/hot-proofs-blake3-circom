use bellpepper_core::{ConstraintSystem, num::AllocatedNum, SynthesisError, LinearCombination};
use circom_scotia::r1cs::R1CS;
use ff::PrimeField;


/// Copied from `circom_scotia::synthesize` and modified to return an Vector of AllocatedNums
/// instead of a single AllocatedNum.
/// Reference work is Nota-Scotia: https://github.com/nalinbhardwaj/Nova-Scotia
pub fn synthesize_with_vec<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    r1cs: R1CS<F>,
    witness: Option<Vec<F>>,
		n_return: usize,
) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
    //println!("witness: {:?}", witness);
    //println!("num_inputs: {:?}", r1cs.num_inputs);
    //println!("num_aux: {:?}", r1cs.num_aux);
    //println!("num_variables: {:?}", r1cs.num_variables);
    //println!("num constraints: {:?}", r1cs.constraints.len());

    let witness = &witness;

    let mut vars: Vec<AllocatedNum<F>> = vec![];

    for i in 1..r1cs.num_inputs {
        let f: F = {
            match witness {
                None => F::ONE,
                Some(w) => w[i],
            }
        };
        let v = AllocatedNum::alloc(cs.namespace(|| format!("public_{}", i)), || Ok(f))?;

        vars.push(v);
    }

    for i in 0..r1cs.num_aux {
        // Private witness trace
        let f: F = {
            match witness {
                None => F::ONE,
                Some(w) => w[i + r1cs.num_inputs],
            }
        };

        let v = AllocatedNum::alloc(cs.namespace(|| format!("aux_{}", i)), || Ok(f))?;
        vars.push(v);
    }

		assert!(n_return <= vars.len(), "n_return must be less than or equal to the number of variables");
    let output = vars[0..n_return].to_vec();

    let make_lc = |lc_data: Vec<(usize, F)>| {
        let res = lc_data.iter().fold(
            LinearCombination::<F>::zero(),
            |lc: LinearCombination<F>, (index, coeff)| {
                lc + if *index > 0 {
                    (*coeff, vars[*index - 1].get_variable())
                } else {
                    (*coeff, CS::one())
                }
            },
        );
        res
    };

    for (i, constraint) in r1cs.constraints.into_iter().enumerate() {
        cs.enforce(
            || format!("constraint {}", i),
            |_| make_lc(constraint.0),
            |_| make_lc(constraint.1),
            |_| make_lc(constraint.2),
        );
    }

    Ok(output)
}

pub(crate) fn bytes_to_u32_le(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks(4)
        .map(|chunk| {
            let arr: [u8; 4] = chunk.try_into().unwrap_or_else(|_| [0; 4]);
            u32::from_le_bytes(arr)
        })
        .collect()
}
