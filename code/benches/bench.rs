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

        // K = 10
        acc_cmp_s_512_10,
        acc_cmp_s_1024_10,
        acc_cmp_s_2048_10,
        acc_cmp_s_4096_10,
        acc_cmp_s_8196_10,
        acc_cmp_s_16384_10,
        acc_cmp_f_512_10,
        acc_cmp_f_1024_10,
        acc_cmp_f_2048_10,
        acc_cmp_f_4096_10,
        acc_cmp_f_8196_10,
        acc_cmp_f_16384_10,

        // K = 100
        acc_cmp_s_512_100,
        acc_cmp_s_1024_100,
        acc_cmp_s_2048_100,
        acc_cmp_s_4096_100,
        acc_cmp_s_8196_100,
        acc_cmp_s_16384_100,
        acc_cmp_f_512_100,
        acc_cmp_f_1024_100,
        acc_cmp_f_2048_100,
        acc_cmp_f_4096_100,
        acc_cmp_f_8196_100,
        acc_cmp_f_16384_100,

        // K = 1000
        acc_cmp_s_512_1000,
        acc_cmp_s_1024_1000,
        acc_cmp_s_2048_1000,
        acc_cmp_s_4096_1000,
        acc_cmp_s_8196_1000,
        acc_cmp_s_16384_1000,
        acc_cmp_f_512_1000,
        acc_cmp_f_1024_1000,
        acc_cmp_f_2048_1000,
        acc_cmp_f_4096_1000,
        acc_cmp_f_8196_1000,
        acc_cmp_f_16384_1000,
}

criterion_main!(acc, h);
