#![allow(non_snake_case)]

use crate::{group::{point_dot}, PallasPoint, PallasScalar};
use acc_consts::consts::S;

//#[derive(Clone)]
//pub struct CommitKey {
//    pub Gs: Vec<*const PallasPoint>,
//}
//
//impl CommitKey {
//    pub fn new(l: usize) -> CommitKey {
//        let Gs: Vec<*const PallasPoint> = consts::G[0..l].iter().map(|x| x as *const PallasPoint).collect();
//
//        CommitKey { Gs }
//    }
//}

//#[derive(Clone)]
//pub struct CommitKey<'a> {
//    Gs: &'a [PallasPoint],
//}
//
//impl<'a> CommitKey<'a> {
//    pub fn new(l: usize) -> CommitKey<'a> {
//        let Gs = &consts::G[0..l];
//
//        CommitKey { Gs }
//    }
//}
//
//
//pub fn trim(l: usize) -> CommitKey<'a> {
//    CommitKey::new(l)
//}

pub fn commit(w: Option<&PallasScalar>, Gs: &[PallasPoint], ms: &[PallasScalar]) -> PallasPoint {
    assert!(Gs.len() == ms.len(), "Length did not match for pedersen commitment: {}, {}", Gs.len(), ms.len());

    let acc = point_dot(ms, Gs);
    if let Some(w) = w {
        S * w + acc
    } else {
        acc
    }
}

#[cfg(test)]
mod tests {
    use ark_std::UniformRand;
    use rand::Rng;
    use acc_consts::consts;

    use super::*;

    fn test_single_homomorphism<R: Rng>(rng: &mut R, l: usize) {
        // Generate random commit keys
        //let ck = trim(l);
        let Gs = &consts::Gs[0..l];

        // Create random message vectors
        let ms1: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms2: Vec<PallasScalar> = (0..l).map(|_| PallasScalar::rand(rng)).collect();
        let ms_sum: Vec<PallasScalar> =
            ms1.iter().zip(ms2.iter()).map(|(m1, m2)| m1 + m2).collect();

        // Create random hiding factors
        let w1 = PallasScalar::rand(rng);
        let w2 = PallasScalar::rand(rng);

        let inner_sum = commit(Some(&(w1 + w2)), Gs, &ms_sum);
        let outer_sum =
            commit(Some(&w1), Gs, &ms1) + commit(Some(&w2), Gs, &ms2);

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

