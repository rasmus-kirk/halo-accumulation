#![allow(non_snake_case, clippy::let_and_return)]

/// Bulletproofs-style polynomial commitments based on the Discrete Log assumption
use anyhow::{ensure, Result};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ark_poly::DenseUVPolynomial;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::One;
use ark_std::UniformRand;
use rand::Rng;
use sha3::{Digest, Sha3_256};

use crate::{
    consts::{D, GS, H, S},
    group::{
        construct_powers, point_dot, rho_0, scalar_dot, PallasPoint, PallasPoly, PallasScalar,
    },
    pedersen,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalProof {
    Ls: Vec<PallasPoint>,
    Rs: Vec<PallasPoint>,
    U: PallasPoint,
    c: PallasScalar,
    C_bar: Option<PallasPoint>,
    w_prime: Option<PallasScalar>,
}

// Helper trait
pub(crate) trait VecPushOwn<T> {
    fn push_own(self, value: T) -> Self;
}

impl<T> VecPushOwn<T> for Vec<T> {
    fn push_own(mut self, value: T) -> Self {
        self.push(value);
        self
    }
}

#[derive(Clone, CanonicalSerialize)]
pub struct HPoly {
    pub(crate) xis: Vec<PallasScalar>,
}

impl HPoly {
    pub fn new(xis: Vec<PallasScalar>) -> Self {
        Self { xis }
    }

    /// Constructs the polynomial h(X) based on the formula:
    /// h(X) := π^(lg(n)-1)_(i=0) (1 + ξ_(lg(n)−i) · X^(2^i)) ∈ F_q[X]
    pub fn get_poly(&self) -> DensePolynomial<PallasScalar> {
        let mut h = DensePolynomial::from_coefficients_slice(&[PallasScalar::one()]); // Start with 1
        let lg_n = self.xis.len() - 1;

        for i in 0..lg_n {
            // Compute 2^i
            let power = 1 << i;

            // Create coefficients for 1 + ξ_(lg(n)-i) * X^(2^i)
            let mut term = vec![PallasScalar::ZERO; power + 1];
            term[0] = PallasScalar::one(); // Constant term 1
            term[power] = self.xis[lg_n - i]; // Coefficient for X^(2^i)

            // Create polynomial for this term
            let poly = DensePolynomial::from_coefficients_vec(term);

            // Multiply the current h(X) with the new term
            h = h * poly;
        }

        h
    }

    pub fn eval(&self, z: &PallasScalar) -> PallasScalar {
        let lg_n = self.xis.len() - 1;
        let one = PallasScalar::one();

        let mut v = one + self.xis[lg_n] * z;
        let mut z_i = *z;

        for i in 1..lg_n {
            z_i.square_in_place();
            v *= one + self.xis[lg_n - i] * z_i;
        }
        v
    }
}

/// Creates a commitment to the coefficients of the polynomial $p$ of degree $d' < d$, with optional hiding $\o$, using pedersen commitments.
///
/// p: A univariate polynomial p(X),
/// d: A degree bound for p, we require that p.degree() <= d,
/// w: Optional hiding to pass to the underlying Pederson Commitment
pub fn commit(p: &PallasPoly, d: usize, w: Option<&PallasScalar>) -> PallasPoint {
    let n = d + 1;

    assert!(n.is_power_of_two());
    assert!(p.degree() <= d);
    assert!(d <= D);

    let mut coeffs = p.coeffs.clone();
    coeffs.resize(n, PallasScalar::ZERO);

    pedersen::commit(w, &GS[0..n], &coeffs)
}

/// Creates a proof that states: "I know a polynomial p of degree d' less than d, with commitment C s.t. p(z) = v" where p is private and d, z, v are public.
///
/// rng: Required since the function uses randomness
/// p: A univariate polynomial p(X)
/// C: A commitment to p,
/// d: A degree bound for p, we require that p.degree() <= d,
/// z: An evaluation point z
/// w: Commitment randomness ω for the Pedersen Commitment C
pub fn open<R: Rng>(
    rng: &mut R,
    p: PallasPoly,
    C: PallasPoint,
    d: usize,
    z: &PallasScalar,
    w: Option<&PallasScalar>,
) -> EvalProof {
    let n = d + 1;
    let lg_n = n.ilog2() as usize;
    assert!(n.is_power_of_two());
    assert!(p.degree() <= d);
    assert!(d <= D);

    // 1. Compute the evaluation v := p(z) ∈ Fq.
    let v = p.evaluate(z);

    let (p_prime, C_prime, w_prime, C_bar) = if let Some(w) = w {
        // (2). Sample a random polynomial p_bar ∈ F^(≤d)_q[X] such that p_bar(z) = 0.
        // p_bar(X) = (X - z) * q(X), where q(X) is a uniform random polynomial
        let z_poly = PallasPoly::from_coefficients_vec(vec![-*z, PallasScalar::ONE]);
        let q = PallasPoly::rand(p.degree() - 1, rng);
        let p_bar = q * z_poly;
        assert_eq!(p_bar.evaluate(z), PallasScalar::ZERO);
        assert_eq!(p_bar.degree(), p.degree());

        // (3). Sample corresponding commitment randomness ω_bar ∈ Fq.
        let w_bar = PallasScalar::rand(rng);

        // (4). Compute a hiding commitment to p_bar: C_bar ← CM.Commit^(ρ0)(ck, p_bar; ω_bar) ∈ G.
        let C_bar = commit(&p_bar, d, Some(&w_bar));

        // (5). Compute the challenge α := ρ(C, z, v, C_bar) ∈ F^∗_q.
        let a = rho_0![C, z, v, C_bar];

        // 6. Compute the polynomial p' := p + α ⋅ p_bar = Σ^d_(i=0) c_i ⋅ X_i ∈ Fq[X].
        let p_prime = p + &p_bar * a;

        // 7. Compute commitment randomness ω' := ω + α ⋅ ω_bar ∈ Fq.
        let w_prime = w_bar * a + w;

        // 8. Compute a non-hiding commitment to p' : C' := C + α ⋅ C_bar - ω' ⋅ S ∈ G.
        let C_prime = C + C_bar * a - S * w_prime;

        (p_prime, C_prime, Some(w_prime), Some(C_bar))
    } else {
        // 6. Compute the polynomial p' := p + α ⋅ p_bar = Σ^d_(i=0) c_i ⋅ X_i ∈ Fq[X].
        let p_prime = p;

        // 8. Compute a non-hiding commitment to p' : C' := C + α ⋅ C_bar - ω' ⋅ S ∈ G.
        let C_prime = C;

        (p_prime, C_prime, None, None)
    };

    // Compute the 0-th challenge field element ξ_0 := ρ0(C', z, v) ∈ F_q, and use it to compute the group element
    // H' := ξ_0 ⋅ H ∈ G. Initialize the following vectors:
    // c_0 := (c_0, c_1, . . . , c_d) ∈ F^(d+1)_q
    // z_0 := (1, z, . . . , z^d) ∈ F^(d+1)_q
    // G_0 := (G_0, G_1, . . . , G_d) ∈ G_(d+1)
    let mut xi_i = rho_0![C_prime, z, v];
    let H_prime = H * xi_i;

    let mut cs = p_prime.coeffs;
    cs.resize(n, PallasScalar::ZERO);
    let mut gs: Vec<PallasPoint> = GS[0..n].iter().map(|x| PallasPoint::from(*x)).collect();
    let mut zs = construct_powers(z, n);

    let mut Ls = Vec::with_capacity(lg_n);
    let mut Rs = Vec::with_capacity(lg_n);

    let mut m = n / 2;

    // NOTE: i is zero-indexed here, but one-indexed in spec,
    // and that i has been corrected in below comments.
    for _ in 0..lg_n {
        // 1&2. Setting Σ_L := l(G_i) || H', Σ_R := r(G i) || H', compute:
        // L_(i+1) := CM.Commit_(Σ_L)(r(c_i) || ⟨r(c_i), l(z_i)⟩)
        // R_(i+1) := CM.Commit_(Σ_R)(l(c_i) || ⟨l(c_i), r(z_i)⟩)
        let (g_l, g_r) = gs.split_at(m);
        let (c_l, c_r) = cs.split_at(m);
        let (z_l, z_r) = zs.split_at(m);

        let dot_l = scalar_dot(c_r, z_l);
        let L = point_dot(c_r, g_l.to_vec()) + H_prime * dot_l;
        Ls.push(L);

        let dot_r = scalar_dot(c_l, z_r);
        let R = point_dot(c_l, g_r.to_vec()) + H_prime * dot_r;
        Rs.push(R);

        // 3. Generate the (i+1)-th challenge ξ_(i+1) := ρ_0(ξ_i, L_(i+1), R_(i+1)) ∈ F_q.
        let xi_next = rho_0![xi_i, L, R];
        let xi_next_inv = xi_next.inverse().unwrap();
        xi_i = xi_next;

        for j in 0..m {
            // 4. Construct the commitment key for the next round: G_(i+1) := l(G_i) + ξ_(i+1) · r(G_i).
            gs[j] = gs[j] + gs[j + m] * xi_next;
            // 5. Construct commitment inputs for the next round:
            // c_(i+1) := l(c_i) + ξ^(−1)_(i+1) · r(c_i)
            // z_(i+1) := l(z_i) + ξ_(i+1) · r(z_i)
            cs[j] = cs[j] + cs[j + m] * xi_next_inv;
            zs[j] = zs[j] + zs[j + m] * xi_next;
        }

        m /= 2;
    }

    // Finally, set U := G_(log_n), c := c_(log_n), and output the evaluation proof π := (L, R, U, c, C_bar, ω').
    let U = gs[0];
    let c = cs[0];
    let pi = EvalProof {
        Ls,      // L
        Rs,      // R
        c,       // a[0]
        U,       // G[0]
        C_bar,   // For constructing C_prime
        w_prime, // For constructing C_prime
    };

    pi
}

/// Cheaply checks that a proof, pi, is correct. It is not a full check
/// however, since an expensive part of the check is deferred until a later point.
///
/// C: A commitment to p,
/// d: A degree bound for p, we require that p.degree() <= d,
/// z: An evaluation point z
/// v: v = p(z)
/// pi: The evaluation proof
pub fn succinct_check(
    C: PallasPoint,
    d: usize,
    z: &PallasScalar,
    v: &PallasScalar,
    pi: EvalProof,
) -> Result<(HPoly, PallasPoint)> {
    let n = d + 1;
    let lg_n = n.ilog2() as usize;
    ensure!(n.is_power_of_two(), "d+1 is not a power of 2!");
    ensure!(d <= D, "d was larger than D!");

    // 1. Parse rk as (⟨group⟩, S, H, d'), and π as (L, R, U, c, C_bar, ω').
    #[rustfmt::skip]
    let EvalProof { Ls, Rs, U, c, C_bar, w_prime } = pi;

    // 2. Check that d = d'. Irrelevant, we just removed d'
    //ensure!(d == d_prime, "d ≠ d'");

    // 4. Compute the non-hiding commitment C' := C + α · C_bar − ω'· S ∈ G.
    let C_prime = if let Some(C_bar) = C_bar {
        // (3). Compute the challenge α := ρ_0(C, z, v, C_bar) ∈ F^∗_q.
        let a = rho_0![C, z, v, C_bar];

        C + C_bar * a - S * w_prime.unwrap()
    } else {
        C
    };

    // 5. Compute the 0-th challenge ξ_0 := ρ_0(C', z, v), and set H' := ξ_0 · H ∈ G.
    let xi_0 = rho_0![C_prime, z, v];
    let mut xis = Vec::with_capacity(lg_n + 1).push_own(xi_0);

    let H_prime = H * xi_0;

    // 6. Compute the group element C_0 := C' + v · H' ∈ G.
    let mut C_i = C_prime + H_prime * v;

    // 7. For each i ∈ [log_n]:
    for i in 0..lg_n {
        // 7.a Generate the (i+1)-th challenge: ξ_(i+1) := ρ_0(ξ_i, L_i, R_i) ∈ F_q.
        let xi_next = rho_0!(xis[i], Ls[i], Rs[i]);
        xis.push(xi_next);

        // 7.b Compute the (i+1)-th commitment: C_(i+1) := C_i + ξ^(−1)_(i+1) · L_i + ξ_(i+1) · R_i ∈ G.
        C_i += Ls[i] * xi_next.inverse().unwrap() + Rs[i] * xi_next;
    }

    // 8. Define the univariate polynomial h(X) := π^(lg(n))_(i=0) (1 + ξ_(lg(n)−i) · X^(2^i)) ∈ F_q[X].
    let h = HPoly::new(xis);

    // 9. Compute the evaluation v' := c · h(z) ∈ F_q.
    let v_prime = c * h.eval(z);

    // 10. Check that C_(log_n) = CM.Commit_Σ(c || v'), where Σ = (U || H').
    ensure!(
        C_i == U * c + H_prime * v_prime,
        "C_(log_n) ≠ CM.Commit_Σ(c || v')"
    );

    // 11. Output (h, U).
    Ok((h, U))
}

/// The full check on the evaluation proof, pi
///
/// C: A commitment to p,
/// d: A degree bound for p, we require that p.degree() <= d,
/// z: An evaluation point z
/// v: v = p(z)
/// pi: The evaluation proof
pub fn check(
    C: &PallasPoint,
    d: usize,
    z: &PallasScalar,
    v: &PallasScalar,
    pi: EvalProof,
) -> Result<()> {
    // 1. Parse ck as (⟨group⟩, hk, S).
    // 2. Set d' := |hk| - 1.
    // 3. Set rk := (⟨group⟩, S, H, d').

    // 4. Check that PC_DL.SuccinctCheck_ρ0(rk, C, d, z, v, π) accepts and outputs (h, U).
    let (h, U) = succinct_check(*C, d, z, v, pi)?;

    // 5. Check that U = CM.Commit(ck, h_vec), where h_vec is the coefficient vector of the polynomial h.
    let comm = pedersen::commit(None, &GS[0..(d + 1)], &h.get_poly().coeffs);
    ensure!(U == comm, "U ≠ CM.Commit(ck, h_vec)");

    Ok(())
}

#[cfg(test)]
mod tests {
    use ark_std::UniformRand;
    use rand::distributions::Uniform;

    use super::*;

    #[test]
    fn test_test() {
        let mut rng = rand::thread_rng();
        let n_range = Uniform::new(2, 10);
        let n = (2 as usize).pow(rng.sample(&n_range));
        let lg_n = n.ilog2() as usize;
        let one = PallasScalar::one();

        let z = PallasScalar::rand(&mut rng);
        let mut xis = Vec::with_capacity(lg_n + 1);
        for _ in 0..(lg_n + 1) {
            xis.push(PallasScalar::rand(&mut rng));
        }

        let mut v_1 = one + xis[lg_n] * z;
        let mut z_i = z.clone();
        for i in 1..lg_n {
            z_i.square_in_place();
            v_1 *= one + xis[lg_n - i] * z_i;
        }

        let mut v_2 = one;
        for i in 0..lg_n {
            let power: u64 = 1 << i;
            v_2 *= one + xis[lg_n - i] * z.pow([power]);
        }

        assert_eq!(v_1, v_2);
    }

    #[test]
    fn test_u_check() {
        let n = (2 as usize).pow(3);
        let lg_n = n.ilog2() as usize;

        // Generate fake values
        let xis: Vec<PallasScalar> = vec![0, 1, 2, 3]
            .into_iter()
            .map(PallasScalar::from)
            .collect();

        let gs_affine = &GS[0..n];
        let gs: Vec<PallasPoint> = gs_affine.iter().map(|x| PallasPoint::from(*x)).collect();
        let mut gs_mut = gs.clone();

        for i in 0..lg_n {
            let (g_l, g_r) = gs_mut.split_at(gs_mut.len() / 2);

            let xi_next = xis[i + 1];

            let mut g = Vec::with_capacity(g_l.len());
            for j in 0..g_l.len() {
                // 4. Construct the commitment key for the next round: G_(i+1) := l(G_i) + ξ_(i+1) · r(G_i).
                g.push(g_l[j] + g_r[j] * xi_next);
            }
            gs_mut = g;
        }

        let g0_expected: PallasPoint = vec![
            gs[0],
            gs[1] * xis[3],
            gs[2] * xis[2],
            gs[3] * xis[2] * xis[3],
            gs[4] * xis[1],
            gs[5] * xis[1] * xis[3],
            gs[6] * xis[1] * xis[2],
            gs[7] * xis[1] * xis[2] * xis[3],
        ]
        .iter()
        .sum();

        assert_eq!(gs_mut.len(), 1);
        assert_eq!(g0_expected, gs_mut[0]);

        let h = HPoly::new(xis.clone());
        let h_coeffs = h.get_poly().coeffs;
        let U = gs_mut[0];
        let U_prime = pedersen::commit(None, &gs_affine, &h_coeffs);

        let mut xs = Vec::with_capacity(gs.len());
        let mut acc = PallasPoint::ZERO;
        for i in 0..gs.len() {
            acc = acc + gs[i] * h_coeffs[i];
            xs.push(gs[i] * h_coeffs[i])
        }

        assert_eq!(U, U_prime)
    }

    #[test]
    fn test_check() -> Result<()> {
        let mut rng = rand::thread_rng();
        let n = (2 as usize).pow(rng.sample(&Uniform::new(2, 10)));
        let d = n - 1;
        let d_prime = rng.sample(&Uniform::new(1, d));

        // Commit to a random polynomial
        let w = PallasScalar::rand(&mut rng);
        let p = PallasPoly::rand(d_prime, &mut rng);
        let C = commit(&p, d, Some(&w));

        // Generate an evaluation proof
        let z = PallasScalar::rand(&mut rng);
        let v = p.evaluate(&z);
        let pi = open(&mut rng, p, C, d, &z, Some(&w));

        // Verify that check works
        check(&C, d, &z, &v, pi)?;

        Ok(())
    }

    #[test]
    fn test_check_no_hiding() -> Result<()> {
        let mut rng = rand::thread_rng();
        let n = (2 as usize).pow(rng.sample(&Uniform::new(2, 10)));
        let d = n - 1;
        let d_prime = rng.sample(&Uniform::new(1, d));

        // Commit to a random polynomial
        let p = PallasPoly::rand(d_prime, &mut rng);
        let C = commit(&p, d, None);

        // Generate an evaluation proof
        let z = PallasScalar::rand(&mut rng);
        let v = p.evaluate(&z);
        let pi = open(&mut rng, p, C, d, &z, None);

        // Verify that check works
        check(&C, d, &z, &v, pi)?;

        Ok(())
    }

    #[test]
    fn test_construct_h_with_degree_7() {
        let mut rng = rand::thread_rng();
        let n = (2 as usize).pow(3);
        let lg_n = n.ilog2() as usize;
        let xis_len = lg_n + 1;

        let xis: Vec<PallasScalar> = vec![PallasScalar::ZERO; xis_len]
            .iter()
            .map(|_| PallasScalar::rand(&mut rng))
            .collect();
        let coeffs = vec![
            PallasScalar::one(),
            xis[3],
            xis[2],
            xis[2] * xis[3],
            xis[1],
            xis[1] * xis[3],
            xis[1] * xis[2],
            xis[1] * xis[2] * xis[3],
        ];
        let h = HPoly::new(xis);

        assert_eq!(h.get_poly().coeffs, coeffs);
    }
}
