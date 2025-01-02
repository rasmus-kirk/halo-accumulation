#![allow(non_snake_case)]

/// Accumulation scheme based on the Discrete Log assumption, using bulletproofs-style IPP
use anyhow::ensure;
use anyhow::Result;
use ark_ff::PrimeField;
use ark_poly::DenseUVPolynomial;
use ark_poly::Polynomial;
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, Zero};
use rand::Rng;
use sha3::{Digest, Sha3_256};

use crate::{
    consts::S,
    group::{construct_powers, point_dot, rho_1, PallasPoint, PallasPoly, PallasScalar},
    pcdl,
};

/// q in the paper
#[derive(Debug, Clone, PartialEq, Eq)]
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
}

/// acc in the paper
#[derive(Debug, Clone)]
pub struct Accumulator {
    C_bar: PallasPoint,
    d: usize,
    z: PallasScalar,
    v: PallasScalar,
    pi: pcdl::EvalProof,
    pi_V: AccumulatorHiding,
}

/// pi_V in the paper, used for hiding only
#[derive(Debug, Clone)]
pub struct AccumulatorHiding {
    h: PallasPoly,
    U: PallasPoint,
    w: PallasScalar,
}

#[derive(Clone, CanonicalSerialize)]
struct AccumulatedHPolys {
    h_0: Option<PallasPoly>,
    hs: Vec<pcdl::HPoly>,
    alpha: Option<PallasScalar>,
    alphas: Vec<PallasScalar>,
}

impl AccumulatedHPolys {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            h_0: None,
            hs: Vec::with_capacity(capacity),
            alphas: Vec::with_capacity(capacity + 1),
            alpha: None,
        }
    }

    fn set_alpha(&mut self, alpha: PallasScalar) {
        self.alphas = construct_powers(&alpha, self.alphas.capacity());
        self.alpha = Some(alpha)
    }

    // WARNING: This will panic if alphas has not been initialized, but should be fine since this is private
    fn get_poly(&self) -> PallasPoly {
        let mut h = PallasPoly::zero();
        if let Some(h_0) = &self.h_0 {
            h += h_0;
        }
        for i in 0..self.hs.len() {
            h += &(self.hs[i].get_poly() * self.alphas[i + 1]);
        }
        h
    }

    // WARNING: This will panic if alphas has not been initialized, but should be fine since this is private
    fn eval(&self, z: &PallasScalar) -> PallasScalar {
        let mut v = PallasScalar::zero();
        if let Some(h_0) = &self.h_0 {
            v += h_0.evaluate(z);
        }
        for i in 0..self.hs.len() {
            v += self.hs[i].eval(z) * self.alphas[i + 1];
        }
        v
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

/// D: Degree of the underlying polynomials
/// pi_V: Used for hiding
fn common_subroutine(
    d: usize,
    qs: &[Instance],
    pi_V: &AccumulatorHiding,
) -> Result<(PallasPoint, usize, PallasScalar, AccumulatedHPolys)> {
    let m = qs.len();

    // 1. Parse avk as (rk, ck^(1)_(PC)), and rk as (⟨group⟩ = (G, q, G), S, H, D).
    let mut hs = AccumulatedHPolys::with_capacity(m);
    let mut Us = Vec::with_capacity(m);

    // (2). Parse π_V as (h_0, U_0, ω), where h_0(X) = aX + b ∈ F_q[X], U_0 ∈ G, and ω ∈ F_q.
    let AccumulatorHiding { h: h_0, U: U_0, w } = pi_V;
    hs.h_0 = Some(h_0.clone());
    Us.push(*U_0);

    // (3). Check that U_0 is a deterministic commitment to h_0: U_0 = PCDL.Commit_ρ0(ck^(1)_PC, h; ω = ⊥).
    ensure!(
        *U_0 == pcdl::commit(h_0, d, None),
        "U_0 ≠ PCDL.Commit_ρ0(ck^(1)_PC, h_0; ω = ⊥)"
    );

    // 4. For each i ∈ [m]:
    for q in qs {
        // 4.a Parse q_i as a tuple ((C_i, d_i, z_i, v_i), π_i).
        #[rustfmt::skip]
        let Instance { C, d: d_i, z, v, pi } = q;

        // 4.b Compute (h_i(X), U_i) := PCDL.SuccinctCheckρ0(rk, C_i, z_i, v_i, π_i) (see Figure 2).
        let (h_i, U_i) = pcdl::succinct_check(*C, *d_i, z, v, pi.clone())?;
        hs.hs.push(h_i);
        Us.push(U_i);

        // 5. For each i in [n], check that d_i = D. (We accumulate only the degree bound D.)
        ensure!(*d_i == d, "d_i ≠ d");
    }

    // 6. Compute the challenge α := ρ1([h_i, U_i]^n_(i=0)) ∈ F_q.
    hs.set_alpha(rho_1!(hs));

    // 7. Set the polynomial h(X) := Σ^n_(i=0) α^i · h_i(X) ∈ Fq[X].

    // 8. Compute the accumulated commitment C := Σ^n_(i=0) α^i · U_i.
    let C = point_dot(&hs.alphas, Us);

    // 9. Compute the challenge z := ρ1(C, h) ∈ F_q.
    let z = rho_1![C, hs.alpha.unwrap()];

    // 10. Randomize C : C_bar := C + ω · S ∈ G.
    let C_bar = C + S * w;

    // 11. Output (C_bar, d, z, h(X)).
    Ok((C_bar, d, z, hs))
}

pub fn prover<R: Rng>(rng: &mut R, d: usize, qs: &[Instance]) -> Result<Accumulator> {
    // 1. Sample a random linear polynomial h_0 ∈ F_q[X],
    let h_0 = PallasPoly::rand(1, rng);

    // 2. Then compute a deterministic commitment to h_0: U_0 := PCDL.Commit_ρ0(ck_PC, h_0, d; ω = ⊥).
    let U_0 = pcdl::commit(&h_0, d, None);

    // 3. Sample commitment randomness ω ∈ Fq, and set π_V := (h_0, U_0, ω).
    let w = PallasScalar::rand(rng);
    let pi_V = AccumulatorHiding { h: h_0, U: U_0, w };

    // 4. Then, compute the tuple (C_bar, d, z, h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V).
    let (C_bar, d, z, h) = common_subroutine(d, qs, &pi_V)?;

    // 5. Compute the evaluation v := h(z)
    let v = h.eval(&z);

    // 6. Generate the hiding evaluation proof π := PCDL.Open_ρ0(ck_PC, h(X), C_bar, d, z; ω).
    //let pi = pcdl::open(rng, h, C_bar, d, &z, Some(&w));
    let pi = pcdl::open(rng, h.get_poly(), C_bar, d, &z, Some(&w));

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
    ensure!(h.eval(&z) == v, "h(z) = v");

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
    use ark_poly::Polynomial;
    use rand::distributions::Uniform;

    use super::*;

    fn random_instance<R: Rng>(rng: &mut R, d: usize) -> Instance {
        let d_prime = rng.sample(&Uniform::new(1, d));

        // Commit to a random polynomial
        let w = PallasScalar::rand(rng);
        let p = PallasPoly::rand(d_prime, rng);
        let C = pcdl::commit(&p, d, Some(&w));

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
        for i in 0..m {
            println!("{}", i);
            acc = Some(accumulate_random_instance(&mut rng, d, acc)?);
        }

        decider(acc.unwrap())?;

        Ok(())
    }
}
