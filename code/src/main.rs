#![allow(non_snake_case)]

use std::{fs::File, path::Path};

use anyhow::Result;
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::PrimeField;
use ark_pallas::Affine;
use ark_serialize::Write;
use sha3::{Digest, Sha3_256};

mod group;

use group::{PallasPoint, PallasScalar};

// Function to generate a random generator for the Pallas Curve.
// Since the order of the curve is prime, any point that is not the identity point is a generator.
fn get_generator_hash(i: usize) -> PallasPoint {
    let genesis_string = "To understand recursion, one must first understand recursion".as_bytes();

    // Hash `genesis_string` concatinated with `i`
    let mut hasher = Sha3_256::new();
    hasher.update(genesis_string);
    hasher.update(i.to_le_bytes());
    let hash_result = hasher.finalize();

    // Interpret the hash as a scalar field element
    let scalar = PallasScalar::from_le_bytes_mod_order(&hash_result);

    // Generate a uniformly sampled point from the uniformly sampled field element
    PallasPoint::generator() * scalar
}

/// Get public parameters
fn get_pp(n: usize) -> (PallasPoint, PallasPoint, Vec<PallasPoint>) {
    let S = get_generator_hash(0);
    let H = get_generator_hash(1);
    let mut Gs = Vec::with_capacity(n);

    for i in 2..(n + 2) {
        Gs.push(get_generator_hash(i))
    }

    (S, H, Gs)
}

fn format_affine(P: Affine) -> String {
    format!("mk_aff!({:?}, {:?}),\n", P.x.0 .0, P.y.0 .0)
}

fn format_projective(name: &str, P: PallasPoint) -> String {
    format!("{name}: ({:?}, {:?}, {:?})\n", P.x.0 .0, P.y.0 .0, P.z.0 .0)
}

fn log_pp(filepath: &Path, n: usize) -> Result<()> {
    let (S, H, Gs) = get_pp(n);

    let mut output = File::create(filepath)?;
    write!(output, "{}", format_projective("S", S))?;
    write!(output, "{}", format_projective("H", H))?;
    for G in Gs {
        let s = format_affine(G.into_affine());
        write!(output, "{}", s)?;
    }

    Ok(())
}

fn main() {
    println!("Hello, world!");
    let n = 16384;
    log_pp(Path::new("points.txt"), n).unwrap();
}

#[cfg(test)]
mod tests {
    use ark_ff::BigInt;
    use ark_pallas::Fq;

    use super::*;

    macro_rules! mk_aff {
        ($x:tt, $y:tt) => {
            Affine::new_unchecked(
                Fq::new_unchecked(BigInt::new($x)),
                Fq::new_unchecked(BigInt::new($y)),
            )
        };
    }

    #[test]
    fn test_fq_reconstruction() {
        let (_, _, Gs) = get_pp(512);

        for G in Gs {
            let x = G.into_affine().x.0 .0;
            let y = G.into_affine().y.0 .0;
            assert_eq!(mk_aff!(x, y), G.into_affine());
        }
    }
}
