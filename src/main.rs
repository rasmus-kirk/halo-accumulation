use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;

pub mod group;
pub mod pedersen;
pub mod pcdl;

use group::{PallasPoint, PallasScalar};


fn main() {
    let genesis_string = "To understand recursion, one must first understand recursion";
    let x = genesis_string.to_string().into_bytes().len();

    println!("Hello, world! {:?}", x);
}
