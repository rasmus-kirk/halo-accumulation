use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_std::{test_rng, UniformRand};
use criterion::Criterion;

use halo_accumulation::{
    group::{PallasPoly, PallasScalar},
    pcdl::{self}, acc,
};
use rand::Rng;

//const N: usize = 8192;
const N: usize = 512;

fn random_instance<R: Rng>(rng: &mut R, d: usize) -> acc::Instance {
    // Commit to a random polynomial
    let w = PallasScalar::rand(rng);
    let p = PallasPoly::rand(d, rng);
    let c = pcdl::commit(&p, Some(&w));

    // Generate an evaluation proof
    let z = PallasScalar::rand(rng);
    let v = p.evaluate(&z);
    let pi = pcdl::open(rng, p, c, d, &z, Some(&w));

    acc::Instance::new(c, d, z, v, pi)
}

pub fn acc_prover(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;

    let qs = [random_instance(&mut rng, d)];

    c.bench_function("acc_prover", |b| b.iter(|| acc::prover(&mut rng, d, &qs, None)));
}

pub fn acc_verifier(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;

    let qs = [random_instance(&mut rng, d)];
    let acc_new = acc::prover(&mut rng, d, &qs, None).unwrap();

    c.bench_function("acc_verifier", |b| b.iter(|| acc::verifier(d, &qs, None, acc_new.clone())));
}

pub fn acc_decider(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;

    let qs = [random_instance(&mut rng, d)];
    let acc_new = acc::prover(&mut rng, d, &qs, None).unwrap();

    c.bench_function("acc_decider", |b| b.iter(|| acc::decider(acc_new.clone())));
}
