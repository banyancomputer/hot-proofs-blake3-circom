use std::f32::consts::E;

use arecibo::traits::Engine;
use bellpepper_core::{num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError};
use circom_scotia::r1cs::R1CS;
use ff::Field;
use ff::PrimeField;
use ff::PrimeFieldBits;
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use num_traits::Pow;

use crate::MAX_BYTES_PER_BLOCK;

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

    assert!(
        n_return <= vars.len(),
        "n_return must be less than or equal to the number of variables"
    );
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

pub(crate) fn pad_vector_to_min_length<T: Clone>(
    vec: &mut Vec<T>,
    min_length: usize,
    pad_value: T,
) {
    let current_length = vec.len();
    if current_length < min_length {
        let additional_length = min_length - current_length;
        vec.extend(vec![pad_value; additional_length]);
    }
}

pub(crate) fn n_blocks_from_bytes(n_bytes: usize) -> usize {
    (n_bytes + MAX_BYTES_PER_BLOCK - 1) / MAX_BYTES_PER_BLOCK
}

pub(crate) fn format_scalar_blake_hash<E: Engine>(integers: [E::Scalar; 8]) -> Vec<u8> {
    let mut bytes_res = vec![];
    for i in 0..8 {
        let e = integers[8 - 1 - i];
        let bits = e.to_le_bits();

        for b in 0..4 {
            let mut byte = 0;
            for j in 0..8 {
                if bits[(4 - 1 - b) * 8 + j] {
                    byte = byte + (2u8.pow(j as u32));
                }
            }
            bytes_res.push(byte);
        }
    }
    // Not to sure why, but the blake3 library returns the bytes in reverse order and thus we will
    // do the same here
    bytes_res.reverse();
    bytes_res
    // let mut res = E::Scalar::ZERO;

    // // e must be less that 2^32 (8 bytes)
    // // We have to reverse the byte order of each 32-bit word
    // let reverse_little_endian = |e: E::Scalar| {
    //     let bits = e.to_le_bits();
    //     let mut ret = <E as Engine>::Scalar::ZERO;
    //     for i in 0..4 {
    //         let mut byte = <E as Engine>::Scalar::ZERO;
    //         for j in 0..8 {
    //             if bits[i * 8 + j] {
    //                 byte = byte + E::Scalar::from(2u64.pow(j as u32));
    //             }
    //         }
    //         ret = ret + (byte * E::Scalar::from(2u64.pow(((4 - i - 1) * 8) as u32)));
    //     }
    //     ret
    // };
    // for i in 0..8 {
    //     // Get mult = 2^(32 * i)
    //     let mut mult = E::Scalar::ONE;
    //     for _ in 0..(8 - i - 1) {
    //         mult = mult * E::Scalar::from(2u64.pow(32 as u32));
    //     }
    //     res = res + (reverse_little_endian(integers[i]) * mult);
    // }
    // (res, bytes_res)
}

// Alternatively, we have the circom do the reversing...

pub(crate) fn format_bytes(v: &[u8]) -> Vec<String> {
    bytes_to_u32_le(v)
        .iter()
        .map(|x| format!("0x{:08x}", x).to_string())
        .collect::<Vec<String>>()
}
