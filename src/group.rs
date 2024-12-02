use ark_ec::PrimeGroup;
use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_std::{UniformRand, Zero};
use rand::Rng;
use sha3::{Digest, Sha3_256};

pub type PallasPoint = ark_pallas::Projective;
pub type PallasScalar = ark_pallas::Fr;
pub type PallasPoly = DensePolynomial<PallasScalar>;

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
// TODO: Ensure these are not buggy!
macro_rules! hash_to_scalar {
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
        let hash_result = hasher.finalize();

        // Interpret the hash as a scalar field element
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash_result[..32]);
        let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

        scalar
    }};
}

macro_rules! hash_to_point {
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
        let hash_result = hasher.finalize();

        // Interpret the hash as a scalar field element
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash_result[..32]);
        let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

        let new_point = PallasPoint::generator() * scalar;

        new_point
    }};
}

pub(crate) use hash_to_point;
pub(crate) use hash_to_scalar;
