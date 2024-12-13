#![allow(non_snake_case, unused_macros, dead_code, unused_imports)]

use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_poly::univariate::DensePolynomial;
use ark_std::One;

pub type PallasPoint = ark_pallas::Projective;
pub type PallasAffine = ark_pallas::Affine;
pub type PallasScalar = ark_pallas::Fr;
pub type PallasPoly = DensePolynomial<PallasScalar>;

/// Dot product of scalars
pub(crate) fn scalar_dot(xs: &[PallasScalar], ys: &[PallasScalar]) -> PallasScalar {
    xs.iter().zip(ys).map(|(x, y)| x * y).sum()
}

/// Dot product of points
pub(crate) fn point_dot(xs: &[PallasScalar], Gs: Vec<PallasPoint>) -> PallasPoint {
    let Gs: Vec<PallasAffine> = Gs.into_iter().map(|x| x.into_affine()).collect();
    PallasPoint::msm_unchecked(&Gs, xs)
}

/// Dot product of points
pub(crate) fn point_dot_affine(xs: &[PallasScalar], Gs: &[PallasAffine]) -> PallasPoint {
    PallasPoint::msm_unchecked(Gs, xs)
}

/// Given scalar z and length n, computes vector [1, z^1, ..., z^(n-1)]
pub(crate) fn construct_powers(z: &PallasScalar, n: usize) -> Vec<PallasScalar> {
    let mut zs = Vec::with_capacity(n);
    let mut current = PallasScalar::one();
    for _ in 0..n {
        zs.push(current);
        current *= z;
    }
    zs
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
