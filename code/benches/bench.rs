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
        acc_cmp_s_512,
        acc_cmp_s_1024,
        acc_cmp_s_2048,
        acc_cmp_s_4096,
        acc_cmp_s_8196,
        acc_cmp_f_512,
        acc_cmp_f_1024,
        acc_cmp_f_2048,
        acc_cmp_f_4096,
        acc_cmp_f_8196,
}

criterion_main!(acc, h);
