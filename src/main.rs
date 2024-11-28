//use ark_pallas::PallasConfig;
//use ark_pallas::{Affine, Projective};
//use ark_serialize::CanonicalSerializeHashExt;
////use ark_std::rand::Rng;
//use ark_std::UniformRand;
//use ark_ec::CurveGroup;
//use sha3::{Digest, Sha3_256};
use ark_ec::CurveGroup; // Common elliptic curve functionality
use ark_ec::PrimeGroup;
use ark_ff::Field;
use ark_ff::PrimeField;
use ark_pallas::{Affine, Fr, PallasConfig, Projective};
use ark_poly::DenseUVPolynomial;
use ark_serialize::CanonicalSerialize;
use ark_std::One;
// For serialization of curve points
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::{test_rng, UniformRand, Zero}; use group::PallasPoly;
use group::hash_bytes_to_point;
// Random number generation
use rand::Rng;
use sha3::{Digest, Sha3_256};

pub mod group;
pub mod pedersen;

use group::{PallasPoint, PallasScalar};

use crate::group::hash_to_scalar;

fn main() {
    //let mut rng = test_rng();
    let mut rng = rand::thread_rng();

    let point = Projective::rand(&mut rng);

    println!("Hello, world!");
}


const D: u64 = 7;
//const L: u64 = D + 1;
fn h() -> PallasPoint {
    let L = D + 1;
    hash_bytes_to_point(&L.to_le_bytes())
}

struct CommitKey {
    ck_pedersen: pedersen::CommitKey,
    h: PallasPoint,
}

fn trim<R: Rng>(rng: &mut R, d: usize) {
    let ck = pedersen::trim(rng, d - 1);
    let h = h();
    ((ck.clone(), h), (ck, h));
}

fn commit(
    ck: &CommitKey,
    p: &PallasPoly,
    d: usize,
    w: &Option<PallasScalar>,
) -> PallasPoint {
    assert!(p.degree() <= d);
    assert!((d+1).is_power_of_two());
    pedersen::commit(w, &ck.ck_pedersen, &p.coeffs)
}

fn dot_product<F: Field>(vec1: &[F], vec2: &[F]) -> F {
    assert_eq!(vec1.len(), vec2.len(), "Vectors must have the same length");

    let mut acc = F::zero();
    for i in 0..vec1.len() {
        acc += vec1[i] * vec2[i]
    }
    acc
}

fn push_to_slice<T: Clone>(vec: &[T], elem: T) -> Vec<T> {
    let mut ret = vec.to_vec();
    ret.push(elem);
    ret
}

struct EvalProof {
    ls: Vec<PallasPoint>,
    rs: Vec<PallasPoint>,
    u: PallasPoint,
    c: PallasScalar,
    c_bar: PallasPoint,
    w_prime: PallasScalar,
}

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
    let n = d + 1;
    assert!(n.is_power_of_two());
    let lg_n = n.ilog2() as usize;

    // 1. Compute the evaluation v := p(z) ∈ Fq.
    let v = p.evaluate(z);

    // 2. Sample a random polynomial p_bar ∈ F^(≤d)_q[X] such that p_bar(z) = 0.
    let z_poly = PallasPoly::from_coefficients_vec(vec![-*z, PallasScalar::ONE]);
    let q = PallasPoly::rand(d, rng);
    // p_bar(X) = (X - z) * q(X), where q(X) is a uniform random polynomial
    let p_bar = z_poly * q;

    // 3. Sample corresponding commitment randomness ω_bar ∈ Fq.
    let w_bar = PallasScalar::rand(rng);

    // 4. Compute a hiding commitment to p_bar: C_bar ← CM.Commit^(ρ0)(ck, p_bar; ω_bar) ∈ G.
    let C_bar = commit(&ck, &p_bar, d, &Some(w_bar));

    // 5. Compute the challenge α := ρ(C, z, v, C_bar) ∈ F^∗_q.
    let a = hash_to_scalar![C, z, v, C_bar];

    // 6. Compute the polynomial p' := p + α ⋅ p_bar = Σ^d_(i=0) ci ⋅ Xi ∈ Fq[X].
    // NOTE: Not necessary, but here it is:
    // let p_prime = p + p_bar * a;

    // 7. Compute commitment randomness ω' := ω + α ⋅ ω_bar ∈ Fq.
    let w_prime = w_bar * a + w;

    // 8. Compute a non-hiding commitment to p' : C' := C + α ⋅ C_bar −ω' ⋅ S ∈ G.
    let S = ck.ck_pedersen.s;
    let C_prime = C + C_bar * a - S * w_prime;

    // Compute the 0-th challenge field element ξ_0 := ρ_0(C', z, v) ∈ F_q, and use it to compute the group element
    // H' := ξ_0 ⋅ H ∈ G. Initialize the following vectors:
    // c_0 := (c_0, c_1, . . . , c_d) ∈ F^(d+1)_q
    // z_0 := (1, z, . . . , z^d) ∈ F^(d+1)_q
    // G_0 := (G_0, G_1, . . . , G_d) ∈ G_(d+1)
    let xi_0 = hash_to_scalar![C_prime, z, v];
    let mut xis = Vec::with_capacity(lg_n);
    xis.push(xi_0);
    let H_prime = H * xi_0;

    let mut cs = p.coeffs.clone();
    let mut gs = ck.ck_pedersen.hk.clone();
    let mut zs = Vec::with_capacity(d + 1);
    let mut current = PallasScalar::one(); // Start with 1
    for _ in 0..=(d + 1) {
        zs.push(current);
        current *= z; // Compute the next power
    }

    let mut Ls = Vec::with_capacity(lg_n as usize);
    let mut Rs = Vec::with_capacity(lg_n as usize);

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

        let create_sigma = |g: &[PallasPoint]| pedersen::CommitKey {
            hk: push_to_slice(g, H_prime),
            s: ck.ck_pedersen.s,
        };

        let sigma_L = create_sigma(g_l);
        let sigma_R = create_sigma(g_r);

        let L = pedersen::commit(&None, &sigma_L, &push_to_slice(c_r, dot_l));
        let R = pedersen::commit(&None, &sigma_R, &push_to_slice(c_l, dot_r));
        Ls.push(L);
        Rs.push(R);

        // 3. Generate the (i+1)-th challenge ξ_(i+1) := ρ_0(ξi, L_(i+1), R_(i+1)) ∈ F_q.
        let xi_next = hash_to_scalar![xis[i], L, R];
        xis.push(xi_next);
        let xi_next_inv = xi_next.inverse().unwrap();

        let mut g = Vec::with_capacity(g_l.len());
        let mut c = Vec::with_capacity(g_l.len());
        let mut z = Vec::with_capacity(g_l.len());
        for j in 0..g_l.len() {
            // 4. Construct the commitment key for the next round: G_(i+1) := l(G_i) + ξ_(i+1) · r(G_i).
            g[j] = g_l[j] + g_r[j] * xi_next;
            // 5. Construct commitment inputs for the next round:
            // c_(i+1) := l(c_i) + ξ^(−1)_(i+1) · r(c_i)
            // z_(i+1) := l(z_i) + ξ_(i+1) · r(z_i)
            c[j] = c_l[j] + c_r[j] * xi_next_inv;
            z[j] = z_l[j] + z_r[j] * xi_next;
        }
        gs = g;
        cs = c;
        zs = z;
    }

    // Finally, set U := G_(log (d+1)), c := c_(log (d+1)), and output the evaluation proof π := (L, R, U, c, C_bar, ω').
    let u = gs[0];
    let c = cs[0];
    let pi = EvalProof {
        ls: Ls,
        rs: Rs,
        u,
        c,
        c_bar: C_bar,
        w_prime,
    };

    pi
}

/// Constructs the polynomial h(X) based on the formula:
/// h(X) := π^(log(d+1)−1)_(i=0) (1 + ξ_(log(d+1)−i)X^(2^i)) ∈ F_q[X]
///
/// - `xi`: Vec containing ξ values (assumed to have length log2(d+1))
/// - Returns: DensePolynomial over the field
fn construct_h<F: Field>(xi: Vec<F>) -> DensePolynomial<F> {
    let mut h = DensePolynomial::from_coefficients_slice(&[F::one()]); // Start with 1

    for (i, &xi_val) in xi.iter().enumerate() {
        // Create 1 + ξ_{len - i - 1} * X^(2^i)
        let power = 1 << i; // Compute 2^i
        let mut term = vec![F::one(); power + 1]; // Coefficients for X^(2^i) term
        term[power] = xi_val; // Set the coefficient for X^(2^i) to ξ
        let poly = DensePolynomial::from_coefficients_vec(term);

        // Multiply the current h(X) with the new term
        h = h.naive_mul(&poly);
    }

    h
}

fn succinct_check(
    rk: CommitKey,
    C: PallasPoint,
    d: usize,
    z: PallasScalar,
    v: PallasScalar,
    pi: EvalProof,
) -> Option<(PallasPoly, PallasPoint)> {
    let n = d + 1;
    let lg_n = n.ilog2() as usize;

    // 1. Parse rk as (⟨group⟩, S, H, d'), and π as (L, R, U, c, C_bar, ω').
    let S = rk.ck_pedersen.s;
    let H = rk.h;
    let d_prime = rk.ck_pedersen.hk.len();
    let Ls = pi.ls;
    let Rs = pi.rs;
    let U = pi.u;
    let c = pi.c;
    let C_bar = pi.c_bar;
    let w_prime = pi.w_prime;

    // 2. Check that d = d'.
    if d != d_prime {
        return None;
    }

    // 3. Compute the challenge α := ρ_0(C, z, v, C_bar) ∈ F^∗_q.
    let a = hash_to_scalar![C, z, v, C_bar];

    // 4. Compute the non-hiding commitment C' := C + α · C_bar − ω'· S ∈ G.
    let C_prime = C + C_bar * a - S * w_prime;

    // 5. Compute the 0-th challenge ξ_0 := ρ_0(C', z, v), and set H' := ξ_0 · H ∈ G.
    let xi_0 = hash_to_scalar![C_prime, z, v,];
    let mut xis = Vec::with_capacity(lg_n);
    xis.push(xi_0);

    let H_prime = H * xi_0;

    // 6. Compute the group element C_0 := C' + v · H' ∈ G.
    let mut C_i = C_prime + H_prime * v;

    // 7. For each i ∈ [log (d + 1)]:
    for i in 0..lg_n {
        // 7.a Generate the (i+1)-th challenge: ξ_(i+1) := ρ_0(ξ_i, L_i, R_i) ∈ F_q.
        let xi_next = hash_to_scalar!(xis[i], Ls[i], Rs[i]);
        xis.push(xi_next);

        // 7.b Compute the (i+1)-th commitment: C_(i+1) := ξ^(−1)_(i+1) · L_i + C_i + ξ_(i+1) · R_i ∈ G.
        C_i += Ls[i] * xi_next.inverse().unwrap() + Rs[i] * xi_next;
    }

    // 8. Define the univariate polynomial h(X) := π^(log(d+1)−1)_(i=0) (1 + ξ_(log(d+1)−i) X^(2^i)) ∈ F_q[X].
    let h = construct_h(xis);

    // 9. Compute the evaluation v' := c · h(z) ∈ F_q.
    let v_prime = c * h.evaluate(&z);

    // 10. Check that C_(log(d+1)) = CM.Commit_Σ(c || v′), where Σ = (U || H′).
    let sigma = pedersen::CommitKey::new(S, vec![U, H_prime]);
    if C_i != pedersen::commit(&None, &sigma, &vec![c, v_prime]) {
        return None;
    }

    // 11. Output (h, U).
    return Some((h, U));
}
