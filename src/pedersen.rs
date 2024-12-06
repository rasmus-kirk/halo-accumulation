#![allow(non_snake_case)]

use crate::{group::{point_dot, get_generator_hash}, PallasPoint, PallasScalar};

#[derive(Clone)]
pub struct CommitKey {
    pub S: PallasPoint,
    pub Gs: Vec<PallasPoint>,
}

impl CommitKey {
    pub fn new(S: PallasPoint, Gs: Vec<PallasPoint>) -> CommitKey {
        CommitKey { S, Gs }
    }
}

pub fn trim(l: usize) -> CommitKey {
    let mut Gs = Vec::with_capacity(l);
    for i in 0..l {
        Gs.push(get_generator_hash(i));
    }

    let S = get_generator_hash(l);

    CommitKey { S, Gs }
}

pub fn commit(w: Option<&PallasScalar>, ck: &CommitKey, ms: &[PallasScalar]) -> PallasPoint {
    assert!(ck.Gs.len() == ms.len(), "Length did not match for pedersen commitment: {}, {}", ck.Gs.len(), ms.len());

    let acc = point_dot(ms, &ck.Gs);
    if let Some(w) = w {
        ck.S * w + acc
    } else {
        acc
    }
}

#[cfg(test)]
mod tests {
    use ark_std::UniformRand;
    use rand::Rng;

    use super::*;

    fn test_single_homomorphism<R: Rng>(rng: &mut R, l: usize) {
        // Generate random commit keys
        let ck = trim(l);

        // Create random message vectors
        let ms1: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms2: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms_sum: Vec<PallasScalar> =
            ms1.iter().zip(ms2.iter()).map(|(m1, m2)| m1 + m2).collect();

        // Create random hiding factors
        let w1 = PallasScalar::rand(rng);
        let w2 = PallasScalar::rand(rng);

        let inner_sum = commit(Some(&(w1 + w2)), &ck, &ms_sum);
        let outer_sum =
            commit(Some(&w1), &ck, &ms1) + commit(Some(&w2), &ck, &ms2);

        // Check if homomorphism property holds
        assert!(
            inner_sum == outer_sum,
            "The homomorphism property does not hold."
        );
    }

    #[test]
    fn test_homomorphism_property() {
        let mut rng = ark_std::test_rng();
        let ms_len = 64; // Number of message elements
        let tests = 10; // Number of tests run

        for _ in 0..tests {
            test_single_homomorphism(&mut rng, ms_len);
        }
    }
}

