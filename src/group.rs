#![allow(non_snake_case)]

use ark_ec::{PrimeGroup, VariableBaseMSM, CurveGroup};
use ark_ff::PrimeField;
use ark_pallas::Affine;
use ark_poly::univariate::DensePolynomial;
use ark_std::{UniformRand, Zero, One};
use rand::Rng;
use sha3::{Digest, Sha3_256};

pub type PallasPoint = ark_pallas::Projective;
pub type PallasScalar = ark_pallas::Fr;
pub type PallasPoly = DensePolynomial<PallasScalar>;

/// Dot product of scalars
pub fn scalar_dot(xs: &[PallasScalar], ys: &[PallasScalar]) -> PallasScalar {
    xs.iter().zip(ys).map(|(x, y)| x * y).sum()
}

/// Dot product of points
pub fn point_dot(xs: &[PallasScalar], Gs: &[PallasPoint]) -> PallasPoint {
    let Gs: Vec<Affine> = Gs.iter().map(|G| G.into_affine()).collect();
    PallasPoint::msm_unchecked(&Gs, &xs)
}

/// Given scalar z and length n, computes vector [1, z^1, ..., z^(n-1)]
pub fn construct_powers(z: &PallasScalar, n: usize) -> Vec<PallasScalar> {
    let mut zs = Vec::with_capacity(n);
    let mut current = PallasScalar::one();
    for _ in 0..n {
        zs.push(current);
        current *= z;
    }
    zs
}

// Function to generate a random generator for the Pallas Curve.
// Since the order of the curve is prime, any point that is not the identity point is a generator.
pub fn get_generator<R: Rng>(rng: &mut R) -> PallasPoint {
    loop {
        // Generate a random projective point on the curve
        let point = PallasPoint::rand(rng);
        if point != PallasPoint::zero() {
            return point;
        }
    }
}

// Function to generate a random generator for the Pallas Curve.
// Since the order of the curve is prime, any point that is not the identity point is a generator.
// Generated from hashes for security.
pub fn get_generator_hash(i: usize) -> PallasPoint {
    let genesis_string = "To understand recursion, one must first understand recursion";
    let mut data = genesis_string.as_bytes().to_vec();
    data.extend_from_slice(&i.to_le_bytes());

    hash_bytes_to_point(&data)
}

// Takes in an arbitrary slice of data, hashes it, and produces a scalar.
// This is probably secure...
pub fn hash_bytes_to_scalar(data: &[u8]) -> PallasScalar {
    let mut hasher = Sha3_256::new();
    hasher.update(&data);
    let hash_result = hasher.finalize();

    // Interpret the hash as a scalar field element
    let mut hash_bytes = [0u8; 32];
    hash_bytes.copy_from_slice(&hash_result[..32]);
    let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

    scalar
}

// Takes in an arbitrary slice of data, hashes it, and produces a curve point.
// This is probably secure...
pub fn hash_bytes_to_point(data: &[u8]) -> PallasPoint {
    let scalar = hash_bytes_to_scalar(data);
    let new_point = PallasPoint::generator() * scalar;

    new_point
}

// These are ugly, but it really cleans up the implementation
// They just hash either points or scalars to a single scalar and point respectively
macro_rules! rho_0 {
    ($($a:expr),+ $(,)?) => {{
        let mut size = 0;
        $(
            size += $a.compressed_size();
         )+
        let mut data = Vec::with_capacity(size);
        $(
            $a.serialize_compressed(&mut data).unwrap();
         )+

        let mut hasher = Sha3_256::new();
        hasher.update(&data);
        hasher.update(&0u32.to_le_bytes());
        let hash_result = hasher.finalize();

        // Interpret the hash as a scalar field element
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash_result[..32]);
        let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

        scalar
    }};
}

macro_rules! rho_1 {
    ($($a:expr),+ $(,)?) => {{
        let mut size = 0;
        $(
            size += $a.compressed_size();
         )+
        let mut data = Vec::with_capacity(size);
        $(
            $a.serialize_compressed(&mut data).unwrap();
         )+

        let mut hasher = Sha3_256::new();
        hasher.update(&data);
        hasher.update(&1u32.to_le_bytes());
        let hash_result = hasher.finalize();

        // Interpret the hash as a scalar field element
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash_result[..32]);
        let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

        scalar
    }};
}

pub(crate) use rho_0;
pub(crate) use rho_1;
