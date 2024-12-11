use ark_ff::{AdditiveGroup, Field};
use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_std::{test_rng, UniformRand, Zero};
use criterion::{criterion_group, criterion_main, Criterion};

use halo_accumulation::{
    group::{PallasPoly, PallasScalar},
    pcdl::HPoly,
};

const N: usize = 256;
const K: usize = 16;

pub fn h_get_poly(c: &mut Criterion) {
    let mut rng = test_rng();
    let lg_n = N.ilog2() as usize;

    let mut xis = Vec::with_capacity(lg_n + 1);
    for _ in 0..(lg_n + 1) {
        xis.push(PallasScalar::rand(&mut rng))
    }

    let h = HPoly::new(xis);

    c.bench_function("h_get_poly", |b| b.iter(|| h.get_poly()));
}

pub fn h_eval(c: &mut Criterion) {
    let mut rng = test_rng();
    let lg_n = N.ilog2() as usize;

    let mut xis = Vec::with_capacity(lg_n + 1);
    for _ in 0..(lg_n + 1) {
        xis.push(PallasScalar::rand(&mut rng))
    }

    let h = HPoly::new(xis);
    let z = PallasScalar::rand(&mut rng);

    c.bench_function("h_eval", |b| b.iter(|| h.eval(&z)));
}

pub fn h_eval_naive(c: &mut Criterion) {
    let mut rng = test_rng();
    let lg_n = N.ilog2() as usize;

    let mut xis = Vec::with_capacity(lg_n + 1);
    for _ in 0..(lg_n + 1) {
        xis.push(PallasScalar::rand(&mut rng))
    }

    let h = HPoly::new(xis);
    let h_poly = h.get_poly();
    assert_eq!(h_poly.degree(), N - 1);
    let z = PallasScalar::rand(&mut rng);

    c.bench_function("h_eval_naive", |b| b.iter(|| h_poly.evaluate(&z)));
}

pub fn random_poly_eval_naive(c: &mut Criterion) {
    let mut rng = test_rng();

    let h = PallasPoly::rand(N - 1, &mut rng);
    assert_eq!(h.degree(), N - 1);
    let z = PallasScalar::rand(&mut rng);

    c.bench_function("random_poly_eval_naive", |b| b.iter(|| h.evaluate(&z)));
}

pub fn h_eval_multiple(c: &mut Criterion) {
    let mut rng = test_rng();
    let lg_n = N.ilog2() as usize;

    let mut hs = Vec::with_capacity(K);
    let a = PallasScalar::rand(&mut rng);
    for _ in 0..K {
        let mut xis = Vec::with_capacity(lg_n + 1);
        for _ in 0..(lg_n + 1) {
            xis.push(PallasScalar::rand(&mut rng))
        }
        hs.push(HPoly::new(xis));
    }

    let z = PallasScalar::rand(&mut rng);

    pub fn f(z: &PallasScalar, a: &PallasScalar, hs: &[HPoly]) -> PallasScalar {
        let mut v = PallasScalar::ZERO;
        for i in 0..hs.len() {
            v += a.pow([i as u64]) * hs[i].eval(&z);
        }
        let x: PallasScalar = hs.iter().map(|x| x.eval(&z)).sum();
        x
    }

    c.bench_function("h_eval_multiple", |b| b.iter(|| f(&z, &a, &hs)));
}

pub fn h_eval_multiple_naive(c: &mut Criterion) {
    let mut rng = test_rng();
    let lg_n = N.ilog2() as usize;

    let mut hs = Vec::with_capacity(K);
    let a = PallasScalar::rand(&mut rng);
    for _ in 0..K {
        let mut xis = Vec::with_capacity(lg_n + 1);
        for _ in 0..(lg_n + 1) {
            xis.push(PallasScalar::rand(&mut rng))
        }
        hs.push(HPoly::new(xis));
    }

    let z = PallasScalar::rand(&mut rng);

    pub fn f(z: &PallasScalar, a: &PallasScalar, hs: &[HPoly]) -> PallasScalar {
        let mut h = PallasPoly::zero();
        for i in 0..hs.len() {
            h = h + (hs[i].get_poly() * a.pow([i as u64]));
        }
        h.evaluate(&z)
    }

    c.bench_function("h_eval_multiple_naive", |b| b.iter(|| f(&z, &a, &hs)));
}

criterion_group!(
    h_benches,
    h_get_poly,
    h_eval,
    h_eval_naive,
    random_poly_eval_naive,
    h_eval_multiple,
    h_eval_multiple_naive
);

criterion_main!(h_benches);
