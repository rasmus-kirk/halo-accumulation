use ark_poly::{DenseUVPolynomial, Polynomial};
use ark_std::{test_rng, UniformRand};
use criterion::Criterion;

use anyhow::Result;
use halo_accumulation::{
    acc::{self, Accumulator, Instance},
    group::{PallasPoly, PallasScalar},
    pcdl::{self},
};
use rand::Rng;

//const N: usize = 8192;
const N: usize = 512;
const K: usize = 1;

fn random_instance<R: Rng>(rng: &mut R, d: usize) -> acc::Instance {
    // Commit to a random polynomial
    let w = PallasScalar::rand(rng);
    let p = PallasPoly::rand(d, rng);
    let c = pcdl::commit(&p, Some(&w));

    // Generate an evaluation proof
    let z = PallasScalar::rand(rng);
    let v = p.evaluate(&z);
    let pi = pcdl::open(rng, p, c, &z, Some(&w));

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

pub fn acc_hamid_fast(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;
    let mut accs = Vec::with_capacity(K);
    let mut qss = Vec::with_capacity(K);

    let mut acc: Option<Accumulator> = None;

    for _ in 0..K {
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

    fn helper(d: usize, qss: &[Vec<Instance>], accs: Vec<Accumulator>) -> Result<()> {
        let last_acc = accs.last().unwrap().clone();

        for (acc, qs) in accs.into_iter().zip(qss) {
            acc::verifier(d, qs, acc)?;
        }

        acc::decider(last_acc)?;

        Ok(())
    }

    c.bench_function("acc_hamid_fast", |b| {
        b.iter(|| helper(d, &qss, accs.clone()).unwrap())
    });
}

pub fn acc_hamid_slow(c: &mut Criterion) {
    let mut rng = test_rng();
    let d = N - 1;
    let mut accs = Vec::with_capacity(K);

    let mut acc: Option<Accumulator> = None;

    for _ in 0..K {
        let q = random_instance(&mut rng, d);
        let qs = if let Some(acc) = acc {
            vec![acc.into(), q]
        } else {
            vec![q]
        };

        acc = Some(acc::prover(&mut rng, d, &qs).unwrap());

        accs.push(acc.as_ref().unwrap().clone());
    }

    fn helper(accs: Vec<Accumulator>) -> Result<()> {
        for acc in accs.into_iter() {
            acc::decider(acc)?;
        }

        Ok(())
    }

    c.bench_function("acc_hamid_slow", |b| {
        b.iter(|| helper(accs.clone()).unwrap())
    });
}
