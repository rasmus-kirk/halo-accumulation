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
// Generated from hashes for security.
fn get_generator_hash(i: usize) -> PallasPoint {
    let genesis_string = "To understand recursion, one must first understand recursion";
    let mut data = genesis_string.as_bytes().to_vec();
    data.extend_from_slice(&i.to_le_bytes());

    let mut hasher = Sha3_256::new();
    hasher.update(&data);
    let hash_result = hasher.finalize();

    // Interpret the hash as a scalar field element
    let mut hash_bytes = [0u8; 32];
    hash_bytes.copy_from_slice(&hash_result[..32]);
    let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

    let new_point = PallasPoint::generator() * scalar;

    new_point
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

fn format_affine(name: &str, P: Affine) -> String {
    format!(
        "{name}: ({:?}, {:?})\n",
        P.x.into_bigint().0,
        P.y.into_bigint().0
    )
}

fn format_projective(name: &str, P: PallasPoint) -> String {
    format!(
        "{name}: ({:?}, {:?}, {:?})\n",
        P.x.into_bigint().0,
        P.y.into_bigint().0,
        P.z.into_bigint().0
    )
}

fn log_pp(filepath: &Path, n: usize) -> Result<()> {
    let (S, H, Gs) = get_pp(n);

    let mut output = File::create(filepath)?;
    write!(output, "{}", format_projective("S", S))?;
    write!(output, "{}", format_projective("H", H))?;
    for i in 0..Gs.len() {
        let s = format_affine(format!("G_{}", i).as_str(), Gs[i].into_affine());
        write!(output, "{}", s)?;
    }

    Ok(())
}

fn main() {
    println!("Hello, world!");
    let n = 8192;
    log_pp(Path::new("points.txt"), n).unwrap();
}
