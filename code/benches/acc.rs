use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_std::{test_rng, UniformRand};
use criterion::Criterion;

use anyhow::Result;
use halo_accumulation::{
    acc::{self, Accumulator, Instance},
    group::{PallasPoly, PallasScalar},
    pcdl::{self},
};
use rand::{distributions::Uniform, Rng};

//const N: usize = 8192;
const N: usize = 512;
const K: usize = 10;

fn random_instance<R: Rng>(rng: &mut R, d: usize) -> acc::Instance {
    let d_prime = rng.sample(&Uniform::new(1, d));

    // Commit to a random polynomial
    let w = PallasScalar::rand(rng);
    let p = PallasPoly::rand(d_prime, rng);
    let c = pcdl::commit(&p, d, Some(&w));

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

    c.bench_function("acc_prover", |b| b.iter(|| acc::prover(&mut rng, d, &qs)));
}

pub fn acc_verifier(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;

    let qs = [random_instance(&mut rng, d)];
    let acc = acc::prover(&mut rng, d, &qs).unwrap();

    c.bench_function("acc_verifier", |b| {
        b.iter(|| acc::verifier(d, &qs, acc.clone()))
    });
}

pub fn acc_decider(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;

    let qs = [random_instance(&mut rng, d)];
    let acc = acc::prover(&mut rng, d, &qs).unwrap();

    c.bench_function("acc_decider", |b| b.iter(|| acc::decider(acc.clone())));
}

// ----- Comparison Benchmarks ----- //

fn acc_compare_fast_helper(d: usize, qss: &[Vec<Instance>], accs: Vec<Accumulator>) -> Result<()> {
    let last_acc = accs.last().unwrap().clone();

    for (acc, qs) in accs.into_iter().zip(qss) {
        acc::verifier(d, qs, acc)?;
    }

    acc::decider(last_acc)?;

    Ok(())
}

fn acc_compare_fast(n: usize, k: usize) -> (usize, Vec<Vec<Instance>>, Vec<Accumulator>) {
    let mut rng = test_rng();
    let d = n - 1;
    let mut accs = Vec::with_capacity(k);
    let mut qss = Vec::with_capacity(k);

    let mut acc: Option<Accumulator> = None;

    for _ in 0..k {
        let q = random_instance(&mut rng, d);
        let qs = if let Some(acc) = acc {
            vec![acc.into(), q]
        } else {
            vec![q]
        };

        acc = Some(acc::prover(&mut rng, d, &qs).unwrap());

        accs.push(acc.as_ref().unwrap().clone());
        qss.push(qs);
    }
    (d, qss, accs)
}

fn acc_compare_slow_helper(accs: Vec<Accumulator>) -> Result<()> {
    for acc in accs.into_iter() {
        acc::decider(acc)?;
    }

    Ok(())
}

fn acc_compare_slow(n: usize, k: usize) -> Vec<Accumulator> {
    let mut rng = test_rng();
    let d = n - 1;
    let mut accs = Vec::with_capacity(k);

    let mut acc: Option<Accumulator> = None;

    for _ in 0..k {
        let q = random_instance(&mut rng, d);
        let qs = if let Some(acc) = acc {
            vec![acc.into(), q]
        } else {
            vec![q]
        };

        acc = Some(acc::prover(&mut rng, d, &qs).unwrap());

        accs.push(acc.as_ref().unwrap().clone());
    }
    accs
}

pub fn acc_cmp_s_512(c: &mut Criterion) {
    let accs = acc_compare_slow(512, K);
    c.bench_function("acc_cmp_s_512", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_512(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare_fast(512, K);
    c.bench_function("acc_cmp_f_512", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_1024(c: &mut Criterion) {
    let accs = acc_compare_slow(1024, K);
    c.bench_function("acc_cmp_s_1024", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_1024(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare_fast(1024, K);
    c.bench_function("acc_cmp_f_1024", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_2048(c: &mut Criterion) {
    let accs = acc_compare_slow(2048, K);
    c.bench_function("acc_cmp_s_2048", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_2048(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare_fast(2048, K);
    c.bench_function("acc_cmp_f_2048", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_4096(c: &mut Criterion) {
    let accs = acc_compare_slow(4096, K);
    c.bench_function("acc_cmp_s_4096", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_4096(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare_fast(4096, K);
    c.bench_function("acc_cmp_f_4096", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_8196(c: &mut Criterion) {
    let accs = acc_compare_slow(8196, K);
    c.bench_function("acc_cmp_s_8196", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_8196(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare_fast(8196, K);
    c.bench_function("acc_cmp_f_8196", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}
