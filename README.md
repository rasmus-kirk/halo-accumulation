# Halo Accumulation Scheme Rust Implementation

This repository contains a Rust implementation of the accumulation scheme
from the described in the 2020 paper _"Proof-Carrying Data from Accumulation
Schemes"_ by Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, and Nicholas
Spooner. The implementation is mostly written to broaden my own understanding
on the subject of IVC, and should be in no way considered secure or efficient.

## Overview

An accumulation scheme is a cryptographic construct used to "aggregate"
the verification of multiple proofs or statements into a single succinct
proof. The idea is to replace repeated verification of individual proofs with a
more efficient process, where the accumulated proof can be verified succinctly.

Key Objects:
- `Instance`: Generally a claim of some statement encoded in a polynomial commitment scheme.
- `Accumulator`: The central object in the scheme that aggregates information about the verified proofs.

Key Operations:
- `prover`: A process that integrates a new proof or statement into the accumulator.
- `verifier`: Verifies that the prover correctly accumulated the instance `q`, the old accumulator `acc` into the new accumulator `acc*`.
- `decider`: Given that _all_ previous accumulators have been correctly checked using the `verifier`, perform an expensive check.

With the correct runtime bounds, we can construct PCD (Proof-Carrying Data)
and IVC (Incrementally Verifiable Computation).

## Getting Started

### Installation

#### Rust

1. Clone the repository:
   ```bash
   git clone https://github.com/rasmus-kirk/halo-accumulation
   cd halo-accumulation
   ```

2. Build the project:
   ```bash
   cargo build
   ```

3. Run the tests to verify the implementation:
   ```bash
   cargo test
   ```

3. Run the benchmarks:
   ```bash
   cargo benchmark
   ```

#### Nix

This project has integration with [Nix](https://nixos.org/), if nix is
installed with flake support, type `nix develop` to get a reproducible
developement shell for this project.

### Usage

Although not recommended, you can import this module and work with it:

#### Polynomial Commitment Scheme in the Discrete Log setting

```rust
```

#### Accumulation Scheme

```rust
```

## License
This project is licensed under the MIT License. See the `LICENSE` file for details.
