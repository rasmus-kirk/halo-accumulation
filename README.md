This repository accompanies the report *"Investigating IVC with Accumulation
Schemes"*. It explores the theoretical foundation of accumulation schemes
and their application in Incrementally Verifiable Computation (IVC). While
the Rust implementation included here serves as a concrete demonstration of
the theory, the focus remains on the mathematical and cryptographic insights
behind the constructions and benchmarking, _not_ production-grade code.

The theory and code is mostly based on the 2020 paper _"Proof-Carrying Data
from Accumulation Schemes"_ by Benedikt Bünz, Alessandro Chiesa, Pratyush
Mishra, and Nicholas Spooner.

## Background  

### What Are Accumulation Schemes?  

Accumulation schemes are cryptographic primitives that allow for the
incremental verification of multiple computations or proofs. They enable
efficient proof systems by cheaply "accumulating" intermediate results,
which can then be checked in a single, possibly expensive, verification step.

These schemes are particularly relevant in IVC, where a sequence of
computations or proofs needs to be verified succinctly. By using the
accumulation scheme, benchmarking shows significant improvements over naive
series of PCS checks.

### Motivation for This Work  

The `ASDL` allows for an efficient IVC construction despite the linear runtime
of a full PCS check, by leveraging the succinct check in `PCDL`. This means
you can have verification that does not scale linearly with the number of
IVC steps, since the linear computation is only done at the end of the IVC
chain, _not_ at each step. This means that, using a PCS based on Bulletproof's
Inner Product Argument, we can create an IVC construction that does not
depend on a trusted setup.

## Theory Overview  

The report included in this repository covers:  

1. **Prerequisites and Cryptographic Background**  
   - Proof Systems
   - Fiat-Shamir heuristic  
   - SNARKs and Bulletproofs  

2. **Incrementally Verifiable Computation (IVC)**  
   - Introduction to IVC and its applications  
   - An IVC construction using traditional SNARKS with sublinear verification

3. **Polynomial Commitment Schemes (PCS)**  
   - Theory behind PCS and their role in succinct proofs  

4. **Accumulation Schemes (AS)**  
   - How accumulation schemes work  
   - Theoretical properties (completeness, soundness)  

5. **IVC Using Accumulation Schemes**  
   - How accumulation schemes lead to new IVC constructions, without the need for a trusted setup  

6. **The Implementation**  
   - Implementation details for `PCDL`, with a completeness proof and a knowledge extractability discussion  
   - Implementation details for `ASDL`, with soundness and completeness proofs.

7. **Efficiency and Benchmarking**  
   - Comparison between naive PCS and accumulation schemes  
   - Preliminary benchmarking results showing promising results  

## Rust Implementation  

The Rust code provides a concrete implementation of the described accumulation
scheme (`ASDL`) and polynomial commitment scheme (`PCDL`). While the
implementation is not designed for production use, it is a useful tool for
understanding the theory and experimenting with the concepts.

### Developement Environment using Nix

This project has nix support, as such, navigating to `/code` and typing
`nix develop`, will install the necessary rust version, with the correct
formatter and rust-analyzer included.

### Unit Tests

Unit tests can be run with `cargo test` in the `/code` directory.

### Benchmarks

Benchmarks can be run with `cargo benchmark` in the `/code` directory.

### Features  
- **Polynomial Commitment Scheme (`PCDL`)**: Implements commitment, opening, and succinct checking.  
- **Accumulation Scheme (`ASDL`)**: Demonstrates the efficiency of accumulation-based verification.  
- **Benchmarks**: Includes preliminary performance comparisons between naive PCS usage and accumulation schemes.  

## Report  

The full report, *["Investigating IVC with Accumulation
Schemes"](https://halo-accumulation.rasmuskirk.com/report/report.pdf)*,
is included in this repository and provides a detailed explanation of the
theory, constructions, and benchmarks.

## Contributions  

This work is primarily intended for those interested in understanding the
theory behind accumulation schemes and their application to IVC. Contributions
or suggestions for improving the theoretical explanations are welcome.

## License  

This project is licensed under the MIT License. See the `LICENSE` file for details.
