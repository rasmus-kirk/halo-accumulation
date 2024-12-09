#![allow(non_snake_case)]

use std::{fs::File, path::Path};

use anyhow::Result;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_serialize::Write;
use acc_consts::*;

pub mod acc;
pub mod group;
pub mod pcdl;
pub mod pedersen;

use group::{get_generator_hash, PallasPoint, PallasScalar};

fn get_pp(n: usize) -> (PallasPoint, PallasPoint, Vec<PallasPoint>) {
    let S = get_generator_hash(0);
    let H = get_generator_hash(1);
    let mut Gs = Vec::with_capacity(n);

    for i in 2..(n + 2) {
        Gs.push(get_generator_hash(i))
    }

    (S, H, Gs)
}

fn format_point(name: &str, P: PallasPoint) -> String {
    format!("{name}: (\"{:?}\", \"{:?}\", \"{:?}\")\n", P.x, P.y, P.z)
}

fn log_pp(filepath: &Path, n: usize) -> Result<()> {
    let (S, H, Gs) = get_pp(n);

    let mut output = File::create(filepath)?;
    write!(output, "{}", format_point("S", S))?;
    write!(output, "{}", format_point("H", H))?;
    for i in 0..Gs.len() {
        let s = format_point(format!("G_{}", i).as_str(), Gs[i]);
        write!(output, "{}", s)?;
    }

    Ok(())
}

fn main() {
    println!("Hello, world!");
    let n = 1024;
    log_pp(Path::new("points.txt"), n).unwrap();
}
