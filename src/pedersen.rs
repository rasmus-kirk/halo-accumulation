use rand::Rng;

use crate::{group::get_generator, PallasPoint, PallasScalar};

#[derive(Clone)]
pub struct CommitKey {
    pub s: PallasPoint,
    pub hk: Vec<PallasPoint>,
}

impl CommitKey {
    pub fn new(s: PallasPoint, hk: Vec<PallasPoint>) -> CommitKey {
        CommitKey { s, hk }
    }
}

pub fn trim<R: Rng>(rng: &mut R, l: usize) -> CommitKey {
    let mut hk = Vec::with_capacity(l);
    let s = get_generator(rng);

    for _ in 0..l {
        hk.push(get_generator(rng));
    }

    CommitKey { s, hk }
}

pub fn commit(w: &Option<PallasScalar>, ck: &CommitKey, ms: &[PallasScalar]) -> PallasPoint {
    assert!(ck.hk.len() == ms.len());

    let acc_g: PallasPoint = ck.hk.iter().sum();
    let acc_f: PallasScalar = ms.iter().sum();
    let acc = acc_g * acc_f;

    if let Some(w) = w {
        ck.s * w + acc
    } else {
        acc
    }
}

#[cfg(test)]
mod tests {
    use ark_std::UniformRand;

    use super::*;

    fn test_single_homomorphism<R: Rng>(rng: &mut R, l: usize) {
        // Generate random commit keys
        let ck = trim(rng, l);

        // Create random message vectors
        let ms1: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms2: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms_sum: Vec<PallasScalar> =
            ms1.iter().zip(ms2.iter()).map(|(m1, m2)| m1 + m2).collect();

        // Create random hiding factors
        let w1 = PallasScalar::rand(rng);
        let w2 = PallasScalar::rand(rng);

        let inner_sum = commit(&Some(w1 + w2), &ck, &ms_sum);
        let outer_sum =
            commit(&Some(w1), &ck, &ms1) + commit(&Some(w2), &ck, &ms2);

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
        let tests = 50; // Number of tests run

        for _ in 0..tests {
            test_single_homomorphism(&mut rng, ms_len);
        }
    }
}

