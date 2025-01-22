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

const N: usize = 1024;

fn random_instance<R: Rng>(rng: &mut R, d: usize) -> acc::Instance {
    let d_prime = rng.sample(&Uniform::new(d / 2, d));

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

fn acc_compare(n: usize, k: usize) -> (usize, Vec<Vec<Instance>>, Vec<Accumulator>) {
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

pub fn acc_cmp_s_512_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(512, 10);
    c.bench_function("acc_cmp_s_512_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_512_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(512, 10);
    c.bench_function("acc_cmp_f_512_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_1024_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(1024, 10);
    c.bench_function("acc_cmp_s_1024_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_1024_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(1024, 10);
    c.bench_function("acc_cmp_f_1024_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_2048_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(2048, 10);
    c.bench_function("acc_cmp_s_2048_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_2048_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(2048, 10);
    c.bench_function("acc_cmp_f_2048_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_4096_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(4096, 10);
    c.bench_function("acc_cmp_s_4096_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_4096_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(4096, 10);
    c.bench_function("acc_cmp_f_4096_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_8196_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(8192, 10);
    c.bench_function("acc_cmp_s_8196_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_8196_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(8192, 10);
    c.bench_function("acc_cmp_f_8196_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_16384_10(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(16384, 10);
    c.bench_function("acc_cmp_s_16384_10", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_16384_10(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(16384, 10);
    c.bench_function("acc_cmp_f_16384_10", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_512_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(512, 100);
    c.bench_function("acc_cmp_s_512_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_512_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(512, 100);
    c.bench_function("acc_cmp_f_512_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_1024_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(1024, 100);
    c.bench_function("acc_cmp_s_1024_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_1024_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(1024, 100);
    c.bench_function("acc_cmp_f_1024_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_2048_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(2048, 100);
    c.bench_function("acc_cmp_s_2048_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_2048_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(2048, 100);
    c.bench_function("acc_cmp_f_2048_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_4096_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(4096, 100);
    c.bench_function("acc_cmp_s_4096_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_4096_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(4096, 100);
    c.bench_function("acc_cmp_f_4096_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_8196_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(8192, 100);
    c.bench_function("acc_cmp_s_8196_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_8196_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(8192, 100);
    c.bench_function("acc_cmp_f_8196_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_16384_100(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(16384, 100);
    c.bench_function("acc_cmp_s_16384_100", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_16384_100(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(16384, 100);
    c.bench_function("acc_cmp_f_16384_100", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_512_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(512, 1000);
    c.bench_function("acc_cmp_s_512_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_512_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(512, 1000);
    c.bench_function("acc_cmp_f_512_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_1024_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(1024, 1000);
    c.bench_function("acc_cmp_s_1024_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_1024_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(1024, 1000);
    c.bench_function("acc_cmp_f_1024_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_2048_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(2048, 1000);
    c.bench_function("acc_cmp_s_2048_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_2048_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(2048, 1000);
    c.bench_function("acc_cmp_f_2048_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_4096_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(4096, 1000);
    c.bench_function("acc_cmp_s_4096_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_4096_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(4096, 1000);
    c.bench_function("acc_cmp_f_4096_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_8196_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(8192, 1000);
    c.bench_function("acc_cmp_s_8196_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_8196_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(8192, 1000);
    c.bench_function("acc_cmp_f_8196_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_cmp_s_16384_1000(c: &mut Criterion) {
    let (_, _, accs) = acc_compare(16384, 1000);
    c.bench_function("acc_cmp_s_16384_1000", |b| {
        b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
    });
}

pub fn acc_cmp_f_16384_1000(c: &mut Criterion) {
    let (d, qss, accs) = acc_compare(16384, 1000);
    c.bench_function("acc_cmp_f_16384_1000", |b| {
        b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
    });
}
