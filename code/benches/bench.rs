use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

mod h;
use h::*;

criterion_group! {
    name = h;
    config = Criterion::default().sample_size(50).measurement_time(Duration::from_secs(10));
    targets =
        h_get_poly,
        h_eval,
        h_eval_naive,
        random_poly_eval_naive,
        h_eval_multiple,
        h_eval_multiple_naive
}

mod acc;
use acc::*;

criterion_group! {
    name = acc;
    config = Criterion::default().sample_size(50).measurement_time(Duration::from_secs(10));
    targets =
        acc_prover,
        acc_verifier,
        acc_decider,
        acc_hamid_slow,
        acc_hamid_fast,
}

criterion_main!(acc, h);
