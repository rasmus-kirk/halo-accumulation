#![allow(non_snake_case)]

/// Accumulation scheme based on the Discrete Log assumption, using bulletproofs-style IPP

use anyhow::ensure;
use anyhow::Context;
use anyhow::Result;
use ark_ff::{Field, PrimeField};
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, Zero};
use rand::Rng;
use sha3::{Digest, Sha3_256};

use crate::{
    consts::S,
    group::{construct_powers, point_dot, rho_1, PallasPoint, PallasPoly, PallasScalar},
    pcdl::{self},
};

/// q in the paper
#[derive(Clone, PartialEq, Eq)]
pub struct Instance {
    C: PallasPoint,      // Commitment to the coefficints of a polynomial p
    d: usize,            // The degree of p
    z: PallasScalar,     // The point to evaluate p at
    v: PallasScalar,     // The evaluation of p(z) = v
    pi: pcdl::EvalProof, // The proof that p(z) = v
}

impl PartialOrd for Instance {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.z.cmp(&other.z))
    }
}

impl Ord for Instance {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.z.cmp(&other.z)
    }

    fn max(self, other: Self) -> Self where Self: Sized, {
        if self.z > other.z {
            self
        } else {
            other
        }
    }

    fn min(self, other: Self) -> Self where Self: Sized, {
        if self.z < other.z {
            self
        } else {
            other
        }
    }
}

/// acc in the paper
#[derive(Clone)]
pub struct Accumulator {
    C_bar: PallasPoint,
    d: usize,
    z: PallasScalar,
    v: PallasScalar,
    pi: pcdl::EvalProof,
    pi_V: AccumulatorHiding,
}

/// pi_V in the paper, used for hiding only
#[derive(Clone)]
pub struct AccumulatorHiding {
    h: PallasPoly,
    U: PallasPoint,
    w: PallasScalar,
}

#[derive(Clone, CanonicalSerialize)]
pub struct AccumulatedHPolys {
    pub(crate) hs: Vec<pcdl::HPoly>,
    pub(crate) a: Option<PallasScalar>,
}

impl AccumulatedHPolys {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            hs: Vec::with_capacity(capacity),
            a: None,
        }
    }

    fn get_poly(&self) -> Result<PallasPoly> {
        let a = self.a.context("TODO")?;
        let mut h = PallasPoly::zero();
        for i in 0..self.hs.len() {
            h = h + (&self.hs[i].get_poly() * a.pow([i as u64]));
        }
        Ok(h)
    }

    fn eval(&self, z: &PallasScalar) -> Result<PallasScalar> {
        let a = self.a.context("TODO")?;
        let mut v = PallasScalar::zero();
        for i in 0..self.hs.len() {
            v += self.hs[i].eval(z) * a.pow([i as u64]);
        }
        Ok(v)
    }
}

impl Instance {
    pub fn new(
        C: PallasPoint,
        d: usize,
        z: PallasScalar,
        v: PallasScalar,
        pi: pcdl::EvalProof,
    ) -> Self {
        Self { C, d, z, v, pi }
    }
}

impl From<Accumulator> for Instance {
    fn from(acc: Accumulator) -> Instance {
        Instance {
            C: acc.C_bar,
            d: acc.d,
            z: acc.z,
            v: acc.v,
            pi: acc.pi,
        }
    }
}

// TODO: What do you do?
/// D: Degree of the underlying polynomials
/// pi_V: Used for hiding
fn common_subroutine(
    D: usize,
    qs: &[Instance],
    pi_V: &AccumulatorHiding,
) -> Result<(PallasPoint, usize, PallasScalar, AccumulatedHPolys)> {
    let m = qs.len();

    // 1. Parse avk as (rk, ck^(1)_(PC)), and rk as (⟨group⟩ = (G, q, G), S, H, D).
    let mut hs = AccumulatedHPolys::with_capacity(m);
    let mut Us = Vec::with_capacity(m);

    // 2. For each i ∈ [m]:
    for q in qs {
        // 2.a Parse q_i as a tuple ((C_i, d_i, z_i, v_i), π_i).
        let Instance { C, d, z, v, pi } = q;

        // 2.b Compute (h_i(X), U_i) := PCDL.SuccinctCheckρ0(rk, C_i, z_i, v_i, π_i) (see Figure 2).
        let (h_i, U_i) = pcdl::succinct_check(C.clone(), d.clone(), &z, &v, pi.clone())?;
        hs.hs.push(h_i);
        Us.push(U_i);

        // 3. For each i in [n], check that d_i = D. (We accumulate only the degree bound D.)
        ensure!(*d == D, "d_i ≠ D");
    }

    // // (4). Parse π_V as (h_0, U_0, ω), where h_0(X) = aX + b ∈ F_q[X], U_0 ∈ G, and ω ∈ F_q.
    let AccumulatorHiding { h: h_0, U: U_0, w } = pi_V;
    assert_eq!(h_0.degree(), 1);

    // // (5). Check that U_0 is a deterministic commitment to h_0: U_0 = PCDL.Commit_ρ0(ck^(1)_PC, h; ω = ⊥).
    ensure!(
        *U_0 == pcdl::commit(&h_0, None),
        "U_0 ≠ PCDL.Commit_ρ0(ck^(1)_PC, h_0; ω = ⊥)"
    );

    // 6. Compute the challenge α := ρ1([h_i, U_i]^n_(i=0)) ∈ F_q.
    hs.a = Some(rho_1!(hs));

    // 7. Set the polynomial h(X) := Σ^n_(i=0) α^i · h_i(X) ∈ Fq[X].

    // 8. Compute the accumulated commitment C := Σ^n_(i=0) α^i · U_i.
    let C = point_dot(&construct_powers(&hs.a.unwrap(), m), Us);

    // 9. Compute the challenge z := ρ1(C, h) ∈ F_q.
    let z = rho_1![C, hs.a];

    // 10. Randomize C : C_bar := C + ω · S ∈ G.
    let C_bar = C + S * w;

    // 11. Output (C_bar, d, z, h(X)).
    Ok((C_bar, D, z, hs))
}

pub fn prover<R: Rng>(rng: &mut R, d: usize, qs: &[Instance]) -> Result<Accumulator> {
    // 1. Sample a random linear polynomial h_0 ∈ F_q[X],
    let h_0 = PallasPoly::rand(1, rng);

    // 2. Then compute a deterministic commitment to h_0: U_0 := PCDL.Commit_ρ0(ck_PC, h_0, d; ω = ⊥).
    let U_0 = pcdl::commit(&h_0, None);

    // 3. Sample commitment randomness ω ∈ Fq, and set π_V := (h_0, U_0, ω).
    let w = PallasScalar::rand(rng);
    let pi_V = AccumulatorHiding { h: h_0, U: U_0, w };

    // 4. Then, compute the tuple (C_bar, d, z, h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V).
    let (C_bar, d, z, h) = common_subroutine(d, qs, &pi_V)?;

    // 5. Compute the evaluation v := h(z)
    let v = h.eval(&z)?;

    // 6. Generate the hiding evaluation proof π := PCDL.Open_ρ0(ck_PC, h(X), C_bar, d, z; ω).
    //let pi = pcdl::open(rng, h, C_bar, d, &z, Some(&w));
    let pi = pcdl::open(rng, h.get_poly()?, C_bar, d, &z, Some(&w));

    // 7. Finally, output the accumulator acc = ((C_bar, d, z, v), π) and the accumulation proof π_V.
    Ok(Accumulator {
        C_bar,
        d,
        z,
        v,
        pi,
        pi_V,
    })
}

// WARNING: No pi_V argument is mentioned in the protocol!
pub fn verifier(D: usize, qs: &[Instance], acc: Accumulator) -> Result<()> {
    let Accumulator {
        C_bar,
        d,
        z,
        v,
        pi: _,
        pi_V,
    } = acc;

    // 1. The accumulation verifier V computes (C_bar', d', z', h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V)
    let (C_bar_prime, d_prime, z_prime, h) = common_subroutine(D, qs, &pi_V)?;

    // 2. Then checks that C_bar' = C_bar, d' = d, z' = z, and h(z) = v.
    ensure!(C_bar_prime == C_bar, "C_bar' ≠ C_bar");
    ensure!(z_prime == z, "z' = z");
    ensure!(d_prime == d, "d' = d");
    ensure!(h.eval(&z)? == v, "h(z) = v");

    Ok(())
}

pub fn decider(acc: Accumulator) -> Result<()> {
    let Accumulator {
        C_bar,
        d,
        z,
        v,
        pi,
        pi_V: _,
    } = acc;
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

    fn accumulate_random_instance<R: Rng>(
        rng: &mut R,
        d: usize,
        acc: Option<Accumulator>,
    ) -> Result<Accumulator> {
        let q = random_instance(rng, d);
        let qs = if acc.is_some() {
            vec![acc.unwrap().into(), q]
        } else {
            vec![q]
        };

        let acc = prover(rng, d, &qs)?;
        verifier(d, &qs, acc.clone())?;

        Ok(acc)
    }

    #[test]
    fn test_acc_scheme() -> Result<()> {
        let mut rng = rand::thread_rng();
        let n_range = Uniform::new(2, 10);
        let n = (2 as usize).pow(rng.sample(&n_range));
        let d = n - 1;

        let m = rng.sample(&n_range);
        let mut acc = None;
        for _ in 0..m {
            acc = Some(accumulate_random_instance(&mut rng, d, acc)?);
        }

        decider(acc.unwrap())?;

        Ok(())
    }
}
