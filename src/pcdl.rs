/// Bulletproofs-style polynomial commitments based on the Discrete Log assumption
use std::ops::Mul;

use ark_ec::CurveGroup;
use ark_ff::{AdditiveGroup, Field};
use ark_poly::DenseUVPolynomial;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::UniformRand;
use ark_std::{One, Zero};
use group::hash_bytes_to_point;
use group::PallasPoly;
use rand::Rng;
use sha3::{Digest, Sha3_256};

use crate::group::hash_to_scalar;
use crate::*;

#[derive(Clone)]
struct CommitKey {
    ck_pedersen: pedersen::CommitKey,
    h: PallasPoint,
}

impl CommitKey {
    fn new(ck_pedersen: pedersen::CommitKey, h: PallasPoint) -> Self {
        CommitKey { ck_pedersen, h }
    }
}

#[derive(Clone)]
struct EvalProof {
    ls: Vec<PallasPoint>,
    rs: Vec<PallasPoint>,
    u: PallasPoint,
    c: PallasScalar,
    c_bar: PallasPoint,
    w_prime: PallasScalar,
}

trait VecPushOwn<T> {
    fn push_own(self, value: T) -> Self;
}

impl<T> VecPushOwn<T> for Vec<T> {
    fn push_own(mut self, value: T) -> Self {
        self.push(value);
        self
    }
}

const D: u64 = 7;
//const L: u64 = D + 1;

fn h() -> PallasPoint {
    let L = D + 1;
    hash_bytes_to_point(&L.to_le_bytes())
}

fn dot_product<F: Field>(vec1: &[F], vec2: &[F]) -> F {
    assert_eq!(vec1.len(), vec2.len(), "Vectors must have the same length");

    let mut acc = F::zero();
    for i in 0..vec1.len() {
        acc += vec1[i] * vec2[i]
    }
    acc
}

fn trim<R: Rng>(rng: &mut R, d: usize) -> (CommitKey, CommitKey) {
    let ck_pedersen = pedersen::trim(rng, d + 1);
    let h = h();

    let ck_pc = CommitKey { ck_pedersen, h };
    let rk_pc = ck_pc.clone();
    (ck_pc, rk_pc)
}

fn commit(ck: &CommitKey, p: &PallasPoly, w: &Option<PallasScalar>) -> PallasPoint {
    let d = p.degree();
    pedersen::commit(&None, &ck.ck_pedersen, &p.coeffs)
}

/// Constructs the polynomial h(X) based on the formula:
/// h(X) := π^(lg(n)-1)_(i=0) (1 + ξ_(lg(n)−i) · X^(2^i)) ∈ F_q[X]
fn construct_h(xis: Vec<PallasScalar>, lg_n: usize) -> DensePolynomial<PallasScalar> {
    let mut h = DensePolynomial::from_coefficients_slice(&[PallasScalar::one()]); // Start with 1

    for i in 0..lg_n {
        // Compute 2^i
        let power = 1 << i;

        // Create coefficients for 1 + ξ_(lg(n)-i) * X^(2^i)
        let mut term = vec![PallasScalar::zero(); power + 1];
        term[0] = PallasScalar::one(); // Constant term 1
        term[power] = xis[lg_n - i]; // Coefficient for X^(2^i)

        // Create polynomial for this term
        let poly = DensePolynomial::from_coefficients_vec(term);

        //println!("h_info_1 = {:?}", poly);
        //println!("h_info_2 = {}, {}, {}, {}", i, lg_n-(i+1), lg_n-i, power);

        // Multiply the current h(X) with the new term
        h = h * poly;
    }

    h
}

fn point_dot(scalars: &[PallasScalar], points: &[PallasPoint]) -> PallasPoint {
    assert_eq!(scalars.len(), points.len());
    let mut acc = PallasPoint::ZERO;
    for (scalar, point) in scalars.iter().zip(points) {
        acc += *point * scalar
    }
    acc
}

// p.coeffs = a

/// ck: The commitment key ck_PC = (ck, H)
/// p: A univariate polynomial p(X)
/// c: A commitment to p,
/// d: A degree bound
/// z: An evaluation point z
/// w: Commitment randomness ω
fn open<R: Rng>(
    rng: &mut R,
    ck: &CommitKey,
    p: &PallasPoly,
    C: &PallasPoint,
    d: usize,
    z: &PallasScalar,
    w: &PallasScalar,
) -> EvalProof {
    let H = ck.h;
    let S = ck.ck_pedersen.s;
    let n = d + 1;
    assert!(n.is_power_of_two());
    let lg_n = n.ilog2() as usize;

    // 1. Compute the evaluation v := p(z) ∈ Fq.
    let v = p.evaluate(z);

    /* TODO: Readd hiding
    // 2. Sample a random polynomial p_bar ∈ F^(≤d)_q[X] such that p_bar(z) = 0.
    let z_poly = PallasPoly::from_coefficients_vec(vec![-*z, PallasScalar::ONE]);
    let q = PallasPoly::rand(d - 1, rng);
    // p_bar(X) = (X - z) * q(X), where q(X) is a uniform random polynomial
    let p_bar = q * z_poly;
    assert_eq!(p_bar.evaluate(z), PallasScalar::ZERO);
    assert_eq!(p_bar.degree(), p.degree());

    // 3. Sample corresponding commitment randomness ω_bar ∈ Fq.
    let w_bar = PallasScalar::rand(rng);

    // 4. Compute a hiding commitment to p_bar: C_bar ← CM.Commit^(ρ0)(ck, p_bar; ω_bar) ∈ G.
    let C_bar = commit(&ck, &p_bar, &Some(w_bar));

    // 5. Compute the challenge α := ρ(C, z, v, C_bar) ∈ F^∗_q.
    let a = hash_to_scalar![C, z, v, C_bar];

    // 6. Compute the polynomial p' := p + α ⋅ p_bar = Σ^d_(i=0) c_i ⋅ X_i ∈ Fq[X].
    // NOTE: Not necessary, but here it is:
    // let p_prime = p + p_bar * a;

    // 7. Compute commitment randomness ω' := ω + α ⋅ ω_bar ∈ Fq.
    let w_prime = w_bar * a + w;

    // 8. Compute a non-hiding commitment to p' : C' := C + α ⋅ C_bar - ω' ⋅ S ∈ G.
    let C_prime = C + C_bar * a - S * w_prime;
    */
    let C_prime = C;
    let w_prime = PallasScalar::one();
    let C_bar = PallasPoint::ZERO;

    // Compute the 0-th challenge field element ξ_0 := ρ0(C', z, v) ∈ F_q, and use it to compute the group element
    // H' := ξ_0 ⋅ H ∈ G. Initialize the following vectors:
    // c_0 := (c_0, c_1, . . . , c_d) ∈ F^(d+1)_q
    // z_0 := (1, z, . . . , z^d) ∈ F^(d+1)_q
    // G_0 := (G_0, G_1, . . . , G_d) ∈ G_(d+1)
    let xi_0 = hash_to_scalar![C_prime, z, v];
    let mut xis = Vec::with_capacity(lg_n + 1).push_own(xi_0);
    let H_prime = H * xi_0;

    let mut cs = p.coeffs.clone();
    let mut gs = ck.ck_pedersen.hk.clone();

    let mut zs = Vec::with_capacity(n);
    let mut current = PallasScalar::one();
    for _ in 0..n {
        zs.push(current);
        current *= z;
    }

    let mut Ls = Vec::with_capacity(lg_n);
    let mut Rs = Vec::with_capacity(lg_n);

    // NOTE: --- Testing start ---
    let mut ls = Vec::with_capacity(lg_n);
    let mut rs = Vec::with_capacity(lg_n);
    let mut Cs = Vec::with_capacity(lg_n + 1);
    Cs.push(C_prime + H_prime * v);
    assert_eq!(dot_product(&cs, &zs), v);
    assert_eq!(Cs[0], point_dot(&cs, &gs) + H_prime * dot_product(&cs, &zs));
    println!("b{}: {}", 0, Cs[0].into_affine());
    let mut v_i = v;
    // NOTE: --- Testing end ---

    // NOTE: i is zero-indexed here, but one-indexed in spec,
    // and that i has been corrected in below comments.
    for i in 0..lg_n {
        // 1&2. Setting Σ_L := l(G_i) || H', Σ_R := r(G i) || H', compute:
        // L_(i+1) := CM.Commit_(Σ_L)(r(c_i) || ⟨r(c_i), l(z_i)⟩)
        // R_(i+1) := CM.Commit_(Σ_R)(l(c_i) || ⟨l(c_i), r(z_i)⟩)
        let (g_l, g_r) = gs.split_at(gs.len() / 2);
        let (c_l, c_r) = cs.split_at(gs.len() / 2);
        let (z_l, z_r) = zs.split_at(gs.len() / 2);

        let dot_l = dot_product(c_r, z_l);
        let dot_r = dot_product(c_l, z_r);

        let sigma_L = pedersen::CommitKey::new(S, g_l.to_vec().push_own(H_prime));
        let sigma_R = pedersen::CommitKey::new(S, g_r.to_vec().push_own(H_prime));

        let L = pedersen::commit(&None, &sigma_L, &c_r.to_vec().push_own(dot_l));
        let R = pedersen::commit(&None, &sigma_R, &c_l.to_vec().push_own(dot_r));

        //let dot_l = dot_product(c_l, z_r);
        //let dot_r = dot_product(c_r, z_l);

        //let L = point_dot(
        //    &c_l.to_vec().push_own(dot_l),
        //    &g_r.to_vec().push_own(H_prime),
        //);
        //let R = point_dot(
        //    &c_r.to_vec().push_own(dot_r),
        //    &g_l.to_vec().push_own(H_prime),
        //);

        Ls.push(L);
        Rs.push(R);

        // 3. Generate the (i+1)-th challenge ξ_(i+1) := ρ_0(ξ_i, L_(i+1), R_(i+1)) ∈ F_q.
        let xi_next = hash_to_scalar![xis[i], L, R];
        let xi_next_inv = xi_next.inverse().unwrap();
        xis.push(xi_next);

        // NOTE: --- Testing start ---
        ls.push(dot_l);
        rs.push(dot_r);
        v_i += xi_next * dot_l + xi_next_inv * dot_r;
        Cs.push(Cs[i] + (L * xi_next_inv) + (R * xi_next));
        assert_eq!(Cs[i], point_dot(&cs, &gs) + H_prime * dot_product(&cs, &zs));
        // NOTE: --- Testing end ---

        println!("a{}: {}", i + 1, Cs[i + 1].into_affine());

        let mut g = Vec::with_capacity(g_l.len());
        let mut c = Vec::with_capacity(g_l.len());
        let mut z = Vec::with_capacity(g_l.len());
        for j in 0..g_l.len() {
            // 4. Construct the commitment key for the next round: G_(i+1) := l(G_i) + ξ_(i+1) · r(G_i).
            g.push(g_l[j] + g_r[j] * xi_next);
            // 5. Construct commitment inputs for the next round:
            // c_(i+1) := l(c_i) + ξ^(−1)_(i+1) · r(c_i)
            // z_(i+1) := l(z_i) + ξ_(i+1) · r(z_i)
            c.push(c_l[j] + c_r[j] * xi_next_inv);
            z.push(z_l[j] + z_r[j] * xi_next);
        }
        gs = g;
        cs = c;
        zs = z;
    }
    println!();

    // NOTE: --- Testing start ---
    let mut lr = PallasScalar::ZERO;
    for i in 0..ls.len() {
        lr += xis[i + 1] * ls[i];
        lr += xis[i + 1].inverse().unwrap() * rs[i];
    }
    // NOTE: --- Testing end ---

    assert_eq!(v_i - lr, v);

    // Finally, set U := G_(log_n), c := c_(log_n), and output the evaluation proof π := (L, R, U, c, C_bar, ω').
    let u = gs[0];
    let c = cs[0];
    let pi = EvalProof {
        ls: Ls,       // L
        rs: Rs,       // R
        c,            // a[0]
        u,            // G[0]
        c_bar: C_bar, // ??? (hiding)
        w_prime,      // ??? (hiding)
    };

    pi
}

fn succinct_check(
    rk: (PallasPoint, PallasPoint, usize),
    C: &PallasPoint,
    d: usize,
    z: &PallasScalar,
    v: &PallasScalar,
    pi: EvalProof,
    rk_pc: &CommitKey,
) -> Result<(PallasPoly, PallasPoint), String> {
    let n = d + 1;
    let lg_n = n.ilog2() as usize;
    assert!(n.is_power_of_two());

    // 1. Parse rk as (⟨group⟩, S, H, d'), and π as (L, R, U, c, C_bar, ω').
    let (S, H, d_prime) = rk;
    let Ls = pi.ls;
    let Rs = pi.rs;
    let U = pi.u;
    let c = pi.c;
    let C_bar = pi.c_bar;
    let w_prime = pi.w_prime;

    // 2. Check that d = d'.
    if d != d_prime {
        return Err("d ≠ d'".to_string());
    };

    // 3. Compute the challenge α := ρ_0(C, z, v, C_bar) ∈ F^∗_q.
    //let a = hash_to_scalar![C, z, v, C_bar];

    // 4. Compute the non-hiding commitment C' := C + α · C_bar − ω'· S ∈ G.
    let C_prime = C; //+ C_bar * a - S * w_prime;

    // 5. Compute the 0-th challenge ξ_0 := ρ_0(C', z, v), and set H' := ξ_0 · H ∈ G.
    let xi_0 = hash_to_scalar![C_prime, z, v];
    let mut xis = Vec::with_capacity(lg_n + 1);
    xis.push(xi_0);

    let H_prime = H * xi_0;

    // 6. Compute the group element C_0 := C' + v · H' ∈ G.
    let mut C_i = C_prime + H_prime * v;
    println!("b{}: {}", 0, C_i.into_affine());

    // 7. For each i ∈ [log_n]:
    for i in 0..lg_n {
        // 7.a Generate the (i+1)-th challenge: ξ_(i+1) := ρ_0(ξ_i, L_i, R_i) ∈ F_q.
        let xi_next = hash_to_scalar!(xis[i], Ls[i], Rs[i]);
        xis.push(xi_next);

        // 7.b Compute the (i+1)-th commitment: C_(i+1) := C_i + ξ^(−1)_(i+1) · L_i + ξ_(i+1) · R_i ∈ G.
        C_i += Ls[i] * xi_next.inverse().unwrap() + Rs[i] * xi_next;
        println!("b{}: {}", i + 1, C_i.into_affine());
    }

    // For testing
    let mut LR = PallasPoint::ZERO;
    for i in 0..Ls.len() {
        let xi_next = hash_to_scalar!(xis[i], Ls[i], Rs[i]);
        LR += Ls[i] * xi_next.inverse().unwrap() + Rs[i] * xi_next;
    }

    let C_0 = C_prime + H_prime * v;
    assert_eq!(Ls.len(), lg_n);
    assert_eq!(Ls.len(), Rs.len());
    assert_eq!(C_0 + LR, C_i);

    // 8. Define the univariate polynomial h(X) := π^(lg(n))_(i=0) (1 + ξ_(lg(n)−i) · X^(2^i)) ∈ F_q[X].
    let h = construct_h(xis, lg_n);

    // 9. Compute the evaluation v' := c · h(z) ∈ F_q.
    let v_prime = c * h.evaluate(&z);

    // 10. Check that C_(log_n) = CM.Commit_Σ(c || v'), where Σ = (U || H').
    let sigma = pedersen::CommitKey::new(S, vec![U, H_prime]);
    let C_other1 = pedersen::commit(&None, &sigma, &vec![c, v_prime]);
    let C_other2 = U * c + H_prime * v_prime;
    println!("other: {:?}", C_other1.into_affine());
    assert_eq!(C_other1, C_other2);
    if C_i != C_other1 {
        return Err("C_(log_n) ≠ CM.Commit_Σ(c || v')".to_string());
    };

    // 11. Output (h, U).
    return Ok((h, U));
}

fn check(
    rk_pc: &CommitKey,
    C: &PallasPoint,
    d: usize,
    z: &PallasScalar,
    v: &PallasScalar,
    pi: EvalProof,
) -> Result<(), String> {
    // 1. Parse ck as (⟨group⟩, hk, S).
    // 2. Set d' := |hk| - 1.
    let d_prime = rk_pc.ck_pedersen.hk.len() - 1;

    // 3. Set rk := (⟨group⟩, S, H, d′).
    let rk = (rk_pc.ck_pedersen.s, rk_pc.h, d_prime);

    // 4. Check that PC_DL.SuccinctCheck_ρ0(rk, C, d, z, v, π) accepts and outputs (h, U).
    let (h, U) = succinct_check(rk, C, d, z, v, pi, rk_pc)?;

    // 5. Check that U = CM.Commit(ck, h_vec), where h_vec is the coefficient vector of the polynomial h.
    if U != pedersen::commit(&None, &rk_pc.ck_pedersen, &h.coeffs) {
        return Err("U ≠ CM.Commit(ck, h_vec)".to_string());
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use ark_ec::CurveGroup;
    use ark_std::{test_rng, UniformRand};
    use rand::distributions::Uniform;

    use super::*;

    #[test]
    fn test_u_check() {
        //let mut rng = rand::thread_rng();
        let mut rng = test_rng();

        let n = (2 as usize).pow(3);
        let lg_n = n.ilog2() as usize;
        let d = n - 1;

        // Generate fake values
        let xis: Vec<PallasScalar> = vec![0, 1, 2, 3]
            .into_iter()
            .map(PallasScalar::from)
            .collect();

        let (ck, _) = trim(&mut rng, d);
        let gs = ck.ck_pedersen.hk.clone();
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

        let h = construct_h(xis.clone(), lg_n);
        let U = gs_mut[0].into_affine();
        let U_prime = pedersen::commit(&None, &ck.ck_pedersen, &h.coeffs).into_affine();

        let mut xs = Vec::with_capacity(gs.len());
        let mut acc = PallasPoint::ZERO;
        for i in 0..gs.len() {
            acc = acc + gs[i] * h.coeffs[i];
            xs.push(gs[i] * h.coeffs[i])
        }

        assert_eq!(U, U_prime)
    }

    #[test]
    fn test_check() -> Result<(), String> {
        //let mut rng = rand::thread_rng();
        let mut rng = test_rng();
        let n_range = Uniform::new(2, 6);
        //let n = (2 as usize).pow(rng.sample(&n_range));
        let n = (2 as usize).pow(3);
        let lg_n = n.ilog2();
        let d = n - 1;
        println!("(d, n, lg_n) = ({}, {}, {})", d, n, lg_n);

        // Generate random commit keys
        let (ck, rk) = trim(&mut rng, d);

        // Commit to a random polynomial
        let w = PallasScalar::rand(&mut rng);
        let p = PallasPoly::rand(d, &mut rng);
        let c = commit(&ck, &p, &Some(w));

        // Generate an evaluation proof
        let z = PallasScalar::rand(&mut rng);
        let w = PallasScalar::rand(&mut rng);
        let v = p.evaluate(&z);
        let pi = open(&mut rng, &ck, &p, &c, d, &z, &w);

        // Verify that check works
        check(&rk, &c, d, &z, &v, pi)?;

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
        let h = construct_h(xis, lg_n);

        assert_eq!(h.coeffs, coeffs);
    }
}
