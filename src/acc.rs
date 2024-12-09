#![allow(non_snake_case)]

use anyhow::ensure;
use anyhow::Result;
use ark_ff::{Field, PrimeField};
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, Zero};
use rand::Rng;
use sha3::{Digest, Sha3_256};

use acc_consts::consts::S;

use crate::{
    group::{construct_powers, point_dot, rho_1, PallasPoint, PallasPoly, PallasScalar},
    pcdl::{self},
};

#[derive(Clone)]
pub struct Instance {
    C: PallasPoint,      // Commitment to the coefficints of a polynomial p
    d: usize,            // The degree of p
    z: PallasScalar,     // The point to evaluate p at
    v: PallasScalar,     // The evaluation of p(z) = v
    pi: pcdl::EvalProof, // The proof that p(z) = v
}

/// q in the paper
impl Instance {}

/// acc in the paper
pub struct Accumulator {
    C_bar: PallasPoint,
    d: usize,
    z: PallasScalar,
    v: PallasScalar,
    pi: pcdl::EvalProof,
}

/// pi_v in the paper
pub struct AccumulationProof {
    h: PallasPoly,
    U: PallasPoint,
    w: PallasScalar,
}

fn common_subroutine(
    D: usize,
    qs: &[Instance],
    pi_V: &AccumulationProof,
) -> Result<(PallasPoint, usize, PallasScalar, PallasPoly)> {
    // 1. Parse avk as (rk, ck^(1)_(PC)), and rk as (⟨group⟩ = (G, q, G), S, H, D).
    let m = qs.len();
    let mut hs = Vec::with_capacity(m);
    let mut Us = Vec::with_capacity(m);

    // 2. For each i ∈ [m]:
    for q in qs {
        // 2.a Parse q_i as a tuple ((C_i, d_i, z_i, v_i), π_i).
        let Instance { C, d, z, v, pi } = q;

        // 2.b Compute (h_i(X), U_i) := PCDL.SuccinctCheckρ0(rk, C_i, z_i, v_i, π_i) (see Figure 2).
        let (h_i, U_i) = pcdl::succinct_check(C.clone(), d.clone(), &z, &v, pi.clone())?;
        hs.push(h_i);
        Us.push(U_i);

        // 3. For each i in [n], check that d_i = D. (We accumulate only the degree bound D.)
        ensure!(*d == D, "d_i ≠ D")
    }

    // (4). Parse π_V as (h_0, U_0, ω), where h_0(X) = aX + b ∈ F_q[X], U_0 ∈ G, and ω ∈ F_q.
    let AccumulationProof { h: h_0, U: U_0, w } = pi_V;
    assert_eq!(h_0.degree(), 1);

    // (5). Check that U_0 is a deterministic commitment to h_0: U_0 = PCDL.Commit_ρ0(ck^(1)_PC, h; ω = ⊥).
    ensure!(*U_0 == pcdl::commit(&h_0, None), "U_0 ≠ PCDL.Commit_ρ0(ck^(1)_PC, h_0; ω = ⊥)");

    // 6. Compute the challenge α := ρ1([h_i, U_i]^n_(i=0)) ∈ F_q.
    let a = rho_1![hs, Us];

    // 7. Set the polynomial h(X) := Σ^n_(i=0) α^i · h_i(X) ∈ Fq[X].
    let mut h = PallasPoly::zero(); // Start with 1
    for i in 0..hs.len() {
        h = h + (&hs[i] * a.pow([i as u64]));
    }

    // 8. Compute the accumulated commitment C := Σ^n_(i=0) α^i · U_i.
    let C = point_dot(&construct_powers(&a, m), &Us);

    // 9. Compute the challenge z := ρ1(C, h) ∈ F_q.
    let z = rho_1![C, h];

    // 10. Randomize C: C_bar := C + ω · S ∈ G.
    let C_bar = C + S * w;

    // 11. Output (C_bar, d, z, h(X)).
    Ok((C_bar, D, z, h))
}

pub fn prove<R: Rng>(
    rng: &mut R,
    d: usize,
    qs: &[Instance],
) -> Result<(Accumulator, AccumulationProof)> {
    // 1. Sample a random linear polynomial h_0 ∈ F_q[X],
    let h_0 = PallasPoly::rand(1, rng);

    // 2. Then compute a deterministic commitment to h_0: U_0 := PCDL.Commit_ρ0(ck_PC, h_0, d; ω = ⊥).
    let U_0 = pcdl::commit(&h_0, None);

    // 3. Sample commitment randomness ω ∈ Fq, and set π_V := (h_0, U_0, ω).
    let w = PallasScalar::rand(rng);
    let pi_V = AccumulationProof { h: h_0, U: U_0, w };

    // 4. Then, compute the tuple (C_bar, d, z, h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V).
    let (C_bar, d, z, h) = common_subroutine(d, qs, &pi_V)?;

    // 5. Compute the evaluation v := h(z)
    let v = h.evaluate(&z);

    // 6. Generate the hiding evaluation proof π := PCDL.Open_ρ0(ck_PC, h(X), C_bar, d, z; ω).
    let pi = pcdl::open(rng, h, C_bar, d, &z, Some(&w));

    // 7. Finally, output the accumulator acc = ((C_bar, d, z, v), π) and the accumulation proof π_V.
    Ok((Accumulator { C_bar, d, z, v, pi }, pi_V))
}

// WARNING: No pi_V argument is mentioned in the protocol!
pub fn verify(
    D: usize,
    qs: &[Instance],
    acc: &Accumulator,
    pi_V: &AccumulationProof,
) -> anyhow::Result<()> {
    let Accumulator {
        C_bar,
        d,
        z,
        v,
        pi: _,
    } = acc;

    // 1. The accumulation verifier V computes (C_bar', d', z', h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V)
    let (C_bar_prime, d_prime, z_prime, h) = common_subroutine(D, &qs, pi_V)?;

    // 2. Then checks that C_bar' = C_bar, d' = d, z' = z, and h(z) = v.
    ensure!(C_bar_prime == *C_bar, "C_bar' ≠ C_bar");
    ensure!(z_prime == *z, "z' = z");
    ensure!(d_prime == *d, "d' = d");
    ensure!(h.evaluate(&z) == *v, "h(z) = v");

    Ok(())
}

pub fn decider(acc: Accumulator) -> Result<()> {
    let Accumulator { C_bar, d, z, v, pi } = acc;
    pcdl::check(&C_bar, d, &z, &v, pi)
}

#[cfg(test)]
mod tests {
    use rand::distributions::Uniform;

    use super::*;

    fn random_instance<R: Rng>(rng: &mut R, d: usize) -> Instance {
        // Commit to a random polynomial
        let w = PallasScalar::rand(rng);
        let p = PallasPoly::rand(d, rng);
        let C = pcdl::commit(&p, Some(&w));

        // Generate an evaluation proof
        let z = PallasScalar::rand(rng);
        let v = p.evaluate(&z);
        let pi = pcdl::open(rng, p, C, d, &z, Some(&w));

        Instance { C, d, z, v, pi }
    }

    #[test]
    fn test_acc_scheme() -> Result<()> {
        let mut rng = rand::thread_rng();
        let n_range = Uniform::new(2, 10);
        let n = (2 as usize).pow(rng.sample(&n_range));
        let d = n - 1;
        let D = d;

        let q = random_instance(&mut rng, d);
        let qs = [q];

        let (acc, pi_V) = prove(&mut rng, D, &qs)?;

        verify(D, &qs, &acc, &pi_V)?;

        decider(acc)?;

        Ok(())
    }
}
