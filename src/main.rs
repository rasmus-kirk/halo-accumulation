use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;

pub mod group;
pub mod pedersen;
pub mod pcdl;
pub mod acc;

use group::{PallasPoint, PallasScalar};


fn main() {
    println!("Hello, world!");
}
