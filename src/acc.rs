#![allow(non_snake_case)]

use ark_ff::{PrimeField, Field};
use ark_poly::{Polynomial, univariate::DensePolynomial, DenseUVPolynomial};
use ark_serialize::CanonicalSerialize;
use ark_std::{One, Zero};
use rand::Rng;
use sha3::{Digest, Sha3_256};

use crate::{
    group::{PallasPoint, PallasScalar, PallasPoly, rho_1, self, point_dot, construct_powers},
    pcdl::{self, SuccinctReceiveKey}, pedersen,
};

#[derive(Clone)]
struct AccVerifyKey {
    rk: pcdl::SuccinctReceiveKey,
    ck_pc_1: pcdl::CommitKey,
}

impl AccVerifyKey {
    fn new(rk: pcdl::SuccinctReceiveKey, ck_pc_1: pcdl::CommitKey) -> Self {
        Self { rk, ck_pc_1 }
    }
}

#[derive(Clone)]
struct AccProveKey {
    ck_pc: pcdl::CommitKey,
    avk: AccVerifyKey,
}

impl AccProveKey {
    fn new(ck_pc: pcdl::CommitKey, avk: AccVerifyKey) -> Self {
        Self { ck_pc, avk }
    }
}

#[derive(Clone)]
struct DecisionKey {
    rk_pc: pcdl::ReceiveKey,
}

impl DecisionKey {
    fn new(rk_pc: pcdl::ReceiveKey) -> Self {
        Self { rk_pc }
    }
}

#[derive(Clone)]
struct Instance {
    C: PallasPoint,      // Commitment to the coefficints of a polynomial p
    d: usize,             // The degree of p
    z: PallasScalar,     // The point to evaluate p at
    v: PallasScalar,     // The evaluation of p(z) = v
    pi: pcdl::EvalProof, // The proof that p(z) = v
}

impl Instance {
    fn new(C: PallasPoint, d: usize, z: PallasScalar, v: PallasScalar, pi: pcdl::EvalProof) -> Self {
        Self { C, d, z, v, pi }
    }
}

/// Does ???
/// D: ???
pub fn indexer(D: usize) -> (AccProveKey, AccVerifyKey, DecisionKey) {
    let (ck_pc, rk_pc) = pcdl::trim(D);
    let pcdl::CommitKey { ck_pedersen: ck, H } = ck_pc.clone();
    let pedersen::CommitKey { S, Gs } = ck;
    let ck_1 = pcdl::trim(1);
    let rk = pcdl::SuccinctReceiveKey::new(S, H, D);

    // TODO: Below line is sus
    let avk = AccVerifyKey::new(rk, ck_1.0);
    let apk = AccProveKey::new(ck_pc, avk.clone());
    let dk = DecisionKey::new(rk_pc);

    (apk, avk, dk)
}

fn common_subroutine(avk: AccVerifyKey, qs: Vec<Instance>, pi_v: (PallasPoly, PallasPoint, PallasScalar)) -> Result<(PallasPoint, usize, PallasScalar, PallasPoly), String> {
    // 1. Parse avk as (rk, ck^(1)_(PC)), and rk as (⟨group⟩ = (G, q, G), S, H, D).
    let AccVerifyKey { rk, ck_pc_1 } = avk;
    let SuccinctReceiveKey { S, H, D } = rk;

    let n = qs.len();
    let mut hs = Vec::with_capacity(n);
    let mut Us = Vec::with_capacity(n);

    // 2. For each i ∈ [n]:
    for q in qs {
        // 2.a Parse q_i as a tuple ((C_i, d_i, z_i, v_i), π_i).
        let Instance { C, d, z, v, pi } = q;

        // 2.b Compute (h_i(X), U_i) := PCDL.SuccinctCheckρ0(rk, C_i, z_i, v_i, π_i) (see Figure 2).
        let (h_i, U_i) = pcdl::succinct_check(&rk, &C, d, &z, &v, pi)?;
        hs.push(h_i);
        Us.push(U_i);

        // 3. For each i in [n], check that d_i = D. (We accumulate only the degree bound D.)
        if d != rk.D {
            return Err("d_i ≠ D".to_string());
        }
    }

    // (4). Parse π_V as (h_0, U_0, ω), where h_0(X) = aX + b ∈ F_q[X], U_0 ∈ G, and ω ∈ F_q.
    let (h_0, U_0, w) = pi_v;
    assert_eq!(h_0.degree(), 1);

    // (5). Check that U_0 is a deterministic commitment to h_0: U_0 = PCDL.Commit_ρ0(ck^(1)_PC, h; ω = ⊥).
    if U_0 != pcdl::commit(&ck_pc_1, &h_0, None) {
        return Err("U_0 ≠ PCDL.Commit_ρ0(ck^(1)_PC, h_0; ω = ⊥)".to_string());
    }

    // 6. Compute the challenge α := ρ1([h_i, U_i]^n_(i=0)) ∈ F_q.
    let a = rho_1![hs, Us];
    
    // 7. Set the polynomial h(X) := Σ^n_(i=0) α^i · h_i(X) ∈ Fq[X].
    let mut h = PallasPoly::zero(); // Start with 1
    for i in 0..hs.len() {
        h = h + (&hs[i] * a.pow([i as u64]));
    }

    // 8. Compute the accumulated commitment C := Σ^n_(i=0) α^i · U_i.
    let C = point_dot(&construct_powers(&a, n), &Us);

    // 9. Compute the challenge z := ρ1(C, h) ∈ F_q.
    let z = rho_1![C, h];

    // 10. Randomize C: C_bar := C + ω · S ∈ G.
    let C_bar = C + S * w;

    // 11. Output (C_bar, d, z, h(X)).
    Ok((C_bar, D, z, h))
}

fn prover<R: Rng>(rng: &mut R, apk: AccProveKey, qs: &[Instance]) {
    let d = apk.avk.rk.D;

    // 1. Sample a random linear polynomial h_0 ∈ F_q[X],
    let h_0 = PallasPoly::rand(apk.avk.rk.D, rng);

    // 2. Then compute a deterministic commitment to h_0: U_0 := PCDL.Commit_ρ0(ck_PC, h_0, d; ω = ⊥).
    
    // 3. Sample commitment randomness ω ∈ Fq, and set π_V := (h_0, U_0, ω). 
    // 4. Then, compute the tuple (C, d, z, h(X)) := T^ρ(avk, [qi]^n_(i=1), π_V).
    // 5. Compute the evaluation v := h(z)
    // 6. Generate the hiding evaluation proof π := PCDL.Open_ρ0(ck_PC, h(X), C_bar, d, z; ω).
    // 7. Finally, output the accumulator acc = ((C_bar, d, z, v), π) and the accumulation proof π_V.

    todo!()
}



/*
fn construct_a(hs: &[PallasPoly], Us: &[PallasPoint]) -> PallasScalar{
        assert!(hs.len() == Us.len());
        assert!(hs.len() > 0);

        let mut size = hs[0].compressed_size() * hs.len() + Us[0].compressed_size() * Us.len();
        let mut data = Vec::with_capacity(size);

        for (h, U) in hs.iter().zip(Us) {
            h.serialize_compressed(data);
            U.serialize_compressed(data);
        }

        let mut hasher = Sha3_256::new();
        hasher.update(&data);
        hasher.update(&1u32.to_le_bytes());
        let hash_result = hasher.finalize();

        // Interpret the hash as a scalar field element
        let mut hash_bytes = [0u8; 32];
        hash_bytes.copy_from_slice(&hash_result[..32]);
        let scalar = PallasScalar::from_le_bytes_mod_order(&hash_bytes);

        scalar
}
*/
