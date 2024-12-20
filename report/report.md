---
title: Investigating IVC with Halo2
date: \today
author: 
  - Rasmus Kirk Jakobsen - 201907084
geometry: margin=2cm
---

\tableofcontents
\newpage

# Introduction

Halo2, can be broken down into the following components:

- **Plonk**: A general-purpose, potentially zero-knowledge, proof scheme.
- **$\PCDL$**: A Polynomial Commitment Scheme in the Discrete Log setting.
- **$\ASDL$**: An Accumulation Scheme in the Discrete Log setting.
- **Pasta**: A Cycle of Elliptic Curves, namely **Pa**llas and Ve**sta**.

This project is focused on the components of $\PCDL$ and $\ASDL$. I used the
[2020 paper](https://example.com) _"Proof-Carrying Data from Accumulation
Schemes"_ as a reference. The project covers both the theoretical aspects
of the scheme described in this document along with a rust implementation,
both of which can be found in the project's [repository](https://example.com).

## Prerequisites

Basic knowledge on elliptic curves, groups, interactive arguments are
assumed in the following text. There is also a heavy reliance on the Inner
Product Proof from the Bulletproofs protocol, see the following resources
on bulletproofs if need be:

- [Section 3 in the original Bulletproofs paper](https://eprint.iacr.org/2017/1066.pdf#section.3)
- [From Zero (Knowledge) to Bulletproofs writeup](https://github.com/AdamISZ/from0k2bp/blob/master/from0k2bp.pdf)
- [Rust Dalek Bulletproofs implementation notes](https://doc-internal.dalek.rs/develop/bulletproofs/notes/inner_product_proof/)
- [Section 4.1 of my bachelors thesis](https://rasmuskirk.com/documents/high-assurance-cryptography-implementing-bulletproofs-in-hacspec.pdf#subsection.4.1)

## Background and Motivation

### Proof Systems

In an Interactive Proof System we have two Interactive Turing machines
the computationally unbounded Prover, P, and the polynomally time bounded
Verifier, V. The Prover tries to convince the Verifier of a statement $x \in L$
language $L \subset \mathbb{B}^*$ in NP. The following properties must be true:

- Completeness: $\forall P \in ITM, x\in L \implies Pr[V_{out} = \bot] \leq \epsilon(x)$

  For all honest provers, P, where $x$ is true, the probability that the
  verifier remains unconvinced is negligible in the length of $x$.

- Soundness: $\forall P^* \in ITM, x \notin L \implies Pr[V_{out} = \top] \leq \epsilon(x)$

  For all provers, honest or otherwise, $P^*$, that tries to convince the
  verifier of a claim, $x$, that is not true, the probability that the
  verifier will be convinced is negligible in the length of $x$.

An Interactive Argument is very similar, but the honest and malicious prover
is now polynomially bounded and receives a Private Auxilliary Input, for
example a witness:

- Completeness: $\forall P(PAI) \in PPT, x\in L \implies Pr[V_{out} = \bot] \leq \epsilon(x)$
- Soundness: $\forall P^* \in PPT, x \notin L \implies Pr[V_{out} = \top] \leq \epsilon(x)$

Proof of knowledge is another type of Proof System, here the prover claims
to know a specific _witness_, $w$, for a statement $x$. Let $x \in L$ and
and $W(x)$ the set of witnesses for $x$ that should be accepted in the
proof. This allows us to define the following relation: $R = \{ (x,w) :
x \in L , w \in W(x) \}$

A proof of knowledge for relation $R$ with is a two party protocol $(P, V)$
with the following two properties:

- **Knowledge Completeness:** $Pr[P(w) \iff V_{out} = 1] = 1$, i.e. as in
  Interactive Proof Systems, after an interaction between the prover and
  verifier the verifier should be convinced with certainty.  
- **Knowledge Soundness:** Loosely speaking, in Knowledge Soundness we have
  an extracter $E$, that when given a possibly malicious prover $P^*$
  as a turing machine has at least as high as the probability that $P^*$
  convinces $V$

The above proof systems may be _zero-knowledge_, which in loose terms means
that anyone looking at the transcript, that is the interaction between
prover and verifier, will not be able to tell the difference between a real
transcript and one that is simulated. This means that an adversary will not
learn any new information, that they could not have gathered themselves. We
can define the property more formally:

- **Zero-knowledge:** $\forall V^*(\delta). \exists S_{V^*}(x) \in PPT. S_{V^*} \sim^C (P,V^*)$

$V^*$ denotes a prover, honest or otherwise, $\d$ represents information
that $V^*$ may have from previous executions of the protocol and $(P,V^*)$
denotes the transcript between the prover and verifier. There is three kinds
of zero-knowledge:

- **Perfect Zero-knowledge:** $\forall V^*(\delta). \exists S_{V^*}(x) \in PPT. S_{V^*} \sim^P (P,V^*)$,
  the transcripts $S_{V^*}(x)$ and $(P,V^*)$ are perfectly indistinguishable.
- **Statistical Zero-knowledge:** $\forall V^*(\delta). \exists S_{V^*}(x) \in PPT. S_{V^*} \sim^S (P,V^*)$,
  the transcripts $S_{V^*}(x)$ and $(P,V^*)$ are statistically indistinguishable.
- **Computational Zero-knowledge:** $\forall V^*(\delta). \exists S_{V^*}(x) \in PPT. S_{V^*} \sim^C (P,V^*)$,
  the transcripts $S_{V^*}(x)$ and $(P,V^*)$ are computationally
  indistinguishable, i.e. no polynomially bounded adversary $\Ac$ can
  distinguish them.

### SNARKS

SNARKs - **S**uccinct **N**on-interactive **AR**guments of **K**nowledge
- have seen increased usage due to their application in blockchains and
cryptocurrencies. They usually also function as so called general-purpose
proof schemes. This means that, given any solution to an NP-problem, it will
produce a proof that the prover knows the solution to said NP-problem. Most
snarks also allow for zero-knowledge arguments, making them zk-SNARKs.

More concretely, imagine that Alice has todays sudoko problem $x$: She
claims to have a solution to this problem, her witness, $w$, and want to
convince Bob without having to send all of it. She could then use a SNARK to
create a proof to convince Bob. To do this she must first encode the sudoku
verifier as a circuit $R_x$, and then give the SNARK prover ($\SNARKProver$)
$R_x(w,w')$ where $w'$ is a public input. This public input could correspond
to the known already known digits for todays sudoku. Finally she can send
this proof, $\pi$, to Bob along with the public sudoku verifying circuit,
$R_x$, and he can check the proof and be convinced using the snark verifier
($\SNARKVerifier$).

Importantly, the succinct part of the name means that the proof size and
verification time must be sublinear. This allows SNARKs to be directly used
for _Incrementally Verifiable Computation_.

### Incrementally Verifiable Computation

Valiant originally described IVC in his [2008
paper](https://iacr.org/archive/tcc2008/49480001/49480001.pdf) in the
following way:

> _\textcolor{GbFg3}{Suppose humanity needs to conduct a very long computation which will span
> superpolynomially many generations. Each generation runs the computation
> until their deaths when they pass on the computational configuration to the
> next generation. This computation is so important that they also pass on a
> proof that the current configuration is correct, for fear that the following
> generations, without such a guarantee, might abandon the project. Can this
> be done?}_

That is, if we run a computation for 100's of years only for it to output 42,
is there a way for us to know that the ouput of said computation is correct,
without taking the time to redo all that computation?

Recently the concept of IVC has seen renewed interest with cryptocurrencies,
as this concept lends itself well to the structure of blockchains. This
allows a blockchain node to omit all previous transaction history in
favour of only a single state, for example, containing all current account
balances. This is a so-called _succinct blockchain_, one such blockchain is
[Mina](https://minaprotocol.com/).

In order to acheive IVC, you need a function $F \in S \to S$ along with some
initial state $z_0 \in S$. Then you can call $F$ to generate a series of
$z$'s, $\vec{z} \in S^{n+1}$:

\begin{figure}[!H]
\centering
\begin{tikzpicture}[node distance=2cm]

    % Nodes
    \node (z0) [node] {$z_0$};
    \node (z1) [node, right=of z0] {$z_1$};
    \node (z2) [node, right=of z1] {$z_2$};
    \node (dots) [right=1cm of z2] {$\dots$};
    \node (zn) [node, right=1cm of dots] {$z_n$};

    % Arrows with labels
    \draw[arrow] (z0) -- node[above] {$F$} (z1);
    \draw[arrow] (z1) -- node[above] {$F$} (z2);
    \draw[arrow] (z2) -- node[above] {$F$} (dots);
    \draw[arrow] (dots) -- node[above] {$F$} (zn);

\end{tikzpicture}
\caption{A visualization of the relationship between $F$ and $\vec{z}$ in a non-IVC setting.}
\end{figure}

In a blockchain setting, you might imagine any $z_i \in \vec{z}$ as a set
of accounts with corresponding balances, and the transition function $F$
as the computation happening when a new block is created and therefore
a new state $z_i$ In the IVC setting, we have a proof, $\pi$, associated
with each state, so that anyone can take just a single pair $(z_m, \pi_m)$
along with the initial state and transition function ($z_0, F$) and verify
that said state was computed correctly.

\begin{figure}[!H]
\centering
\begin{tikzpicture}[node distance=2cm]

    % Nodes
    \node (z0) [node] {$z_0$};
    \node (z1) [node, right=of z0] {$(z_1, \pi_1)$};
    \node (z2) [node, right=of z1] {$(z_2, \pi_2)$};
    \node (dots) [right=1cm of z2] {$\dots$};
    \node (zn) [node, right=1cm of dots] {$(z_n, \pi_n)$};

    % Arrows with labels
    \draw[arrow] (z0) -- node[above] {$F$} (z1);
    \draw[arrow] (z1) -- node[above] {$F$} (z2);
    \draw[arrow] (z2) -- node[above] {$F$} (dots);
    \draw[arrow] (dots) -- node[above] {$F$} (zn);

\end{tikzpicture}
\caption{A visualization of the relationship between $F, \vec{z}$ and $\vec{\pi}$ in an IVC setting.}
\end{figure}

The proof $\pi_i$ describes the following:

> _\textcolor{GbFg3}{"The current state $z_i$ is computed from applying $F$ $i$ times to $z_0$
> ($z_i = F^i(z_0) = F(z_{i-1})$) and the associated proof $\pi_{i-1}$ for
> the previous state is valid."}_

Or more formally, $\pi_i$ is a proof of the following claim expressed as a
circuit $R$:

$$z_i = F(z_{i-1}) \; \land \; (i = 0 \lor \exists \, \pi_{i-1}, \, \text{ s.t. } \SNARKVerifier(z_{i-1}, \pi_{i-1}) = \top)$$

Where $V$ represents the verification circuit in the proof system we're
using. This means, that we're taking the verifier, representing it as a circuit, and
then feeding it to the prover. This is not a trivial task in practice! It
also means that the verification time must be sublinear for IVC to work
properly, otherwise

**TODO**:

- Explain: Otherwise what happens? Blowup?

### Bulletproofs

In 2016, [the Bulletproofs paper](https://eprint.iacr.org/2017/1066.pdf)
was released. Bulletproofs relies on the hardness of the Discrete Logarithm
problem, and allows for an untrusted setup to generate the Common Reference
String. It has logarithmic proof size, and lends itself well efficient range
proofs. It's also possible to generate proofs for arbitrary circuits, but
with less effeciency.

At the heart of Bulletproofs lies the Inner Product Argument (IPA), wherein
a prover proves he knows two vectors, $\vec{a}, \vec{b} \in \Fb_q^n$,
with commitment $C \in \Eb(\Fb_q)$, and their corresponding inner product,
$c = \ip{\vec{a}}{\vec{b}}$. It creates this non-interactive proof,
with only $\lg(n)$ size, by compressing the point and vectors $\lg(n)$
times. Unfortunately, the IPA suffers, and by extension Bulletproofs, suffer
from linear verification time, making them unsuitible for IVC.

### Accumulation Schemes

The authors of [a 2019 paper](https://eprint.iacr.org/2019/1021.pdf)
presented _Halo_ the so-called first practical example of recursive
proof composition without a trusted setup. Using a modified version
of the Bulletproofs-style Inner Product Argument (IPA), they present a
polynomial commitment scheme. Computing the evaluation of a point $z \in
\Fb_q$ on polynomial $p(X) \in \Fb^d_q[X]$ as $v = \ip{\vec{p}}{\vec{z}}$
where $\vec{z} = (z^0, z^1, \dots, z^{d+1})$ and $\vec{p} \in \Fb^d$ is the
coefficient vector of $p(X)$, using the IPA. However, since the the vector
$\vec{z}$ is not private, and has a certain structure, we can split the
verification algorithm in two: $\PCDLSuccinctCheck$ and $\PCDLCheck$. Using
the $\PCDLSuccinctCheck$ we can accumulate $n$ instances, and only perform
the expensive linear check at the end of accumulation.

In the [2020 paper _"Proof-Carrying Data from Accumulation
Schemes"_](https://eprint.iacr.org/2020/499.pdf), that this project
heavily relies on, the authors presented a generalized version of the
previous accumulation structure of Halo that they coined _Accumulation
Schemes_. Simply put, given a predicate $\Phi: X \to \Bb$,
an accumulation scheme consists of the following functions:

- $\ASProver(q_i: X, acc_i: \Acc) \to \Acc$

    The prover accumulates the instance $q_i$ into the previous accumulator
    $acc_{i-1}$ into the new accumulator $acc_i$.

- $\ASVerifier(q_i: X, acc_i: \Acc, acc_{i+1}: \Acc) \to \Result(\top, \bot)$

    The verifier checks that the instance $q_i$ was correctly accumulated
    into the previous accumulator $acc_{i-1}$ to form the new accumulator
    $acc_i$.

- $\ASDecider(acc_{i+1}: \Acc) \to \Result(\top, \bot)$

    The decider performs a single check that simultaneously ensures that
    _every_ previous instance-proof pair accumulated in $acc_{i+1}$ verifies
    assuming the $\ASVerifier$ has accepted that every previous accumulator
    correctly accumulates $q_i$.

We define completeness and soundness for the Accumulation Scheme:

- **Completeness:** For all accumulators $acc_i$ and predicate inputs $q \in X$,
  if $\top = \ASDecider(acc) = \Phi(q)$, then for $\ASProver(q, acc_i)
  = acc_{i+1}$ it holds that $\top = \ASVerifier(acc_i, q, acc_{i+1}) =
  \ASDecider(acc_{i+1})$.

- **Soundness:** For all efficiently-generated accumulators $acc_i, acc_{i+1}
  \in \Acc$ and predicate inputs $q \in X$, if $\top = \ASDecider(acc_{i+1}) =
  \ASVerifier(q, acc_i, acc_{i+1})$ then, with all but negligible probability,
  $\top = \Phi(q) = \ASDecider(acc_i)$.

### IVC from Accumulation Schemes

If the $\ASVerifier$ runtime is sub-linear and we have a $\SNARKVerifierSlow$
that may run in linear time, then we can create an IVC scheme:

- $\IVCProver(z_i: \textbf{Instance}, \pi_i: \textbf{Proof}, acc_i: \Acc) \to (\textbf{Proof}, \Acc)$

  - Accumulates $(z_i, \pi_i)$ with $acc_i$ to obtain a new accumulator $acc_{i+1}$.
  - Then generates a SNARK proof $\pi_{i+1}$ of the following claim, expressed as a circuit $R$:
      $$"z_{i+1} = F(z_i) \; \land \; (i = 0 \lor \exists \, \pi_i, \, acc_i \text{ s.t. } \ASVerifier((z_i, \pi_i), acc_i, acc_{i+1}) = \top)"$$
  - Output $(\pi_{i+1}, acc_{i+1})$

- $\IVCVerifier(\pi_{i+1}: \textbf{Proof}, acc_{i+1}: \Acc) \to \Result(\top, \bot)$

  Checks the proof: $\top \meq \SNARKVerifierSlow(\pi_{i+1}) \meq \ASDecider(acc_{i+1})$

Consider the above chain run $n$ times. As in the "simple" SNARK IVC
construction, if the SNARK verifier accepts at the end, then that means:

$$
\begin{alignedat}[b]{2}
  &\SNARKVerifierSlow(\pi_i)                               &&= \top \then \\
  &\ASVerifier((z_{n-1}, \pi_{n-1}), acc_{n-1}, acc_n)     &&= \top \then \\
  &\ASVerifier((z_{n-2}, \pi_{n-2}), acc_{n-2}, acc_{n-1}) &&= \top \then \cdots \\
  &\ASVerifier((z_0, \pi_0), acc_0, acc_1)                 &&= \top \then \\
\end{alignedat}
$$

Now, by the soundness property of the Accumulation Scheme, and instance
$q \in X$ will be true if $\top = \ASVerifier(q, acc_i, acc_{i+1}) =
\ASDecider(acc_{i+1})$, so if all the accumulators $\vec{acc} \in
\Acc^{n+1}$ are valid, then all the instances will be true. This is exactly
the case however due to the definition of the decider whereby checking an
accumulator $acc_i$ ensures that every previous instance is true, $\Phi(q_i)
= \top$, provided that all previous verifiers accepted.

### General Polynomial Commitment Schemes

In the section above about SNARKs, general-purpose proof schemes were
described. Modern general-purpose (zero-knowledge) proof schemes, such as
Sonic[^1], Plonk[^2] and Marlin[^3], commonly use PCS's _Polynomial Commitment
Schemes_ for creating their proofs. This means that different PCS's can be
used to get security under weaker or stronger assumptions.

<!-- AGM gives you snarks? -->
**TODO**: List the options (AGM?, BP, STARKS).

**TODO**: The assumptions on $d$ seems wrong in the code, not a big deal

A PCS allows a prover to prove to a verifier that a commited polynomial
evaluates to a certain value, $v$, given an evaluation input $z$.There are
three main functions used to prove this ($\PCSetup$ and $\PCTrim$ omitted):

- $\PCCommit(p: \Fb^{d'}_q[X], d: \Nb, \o: \Option(\Fb_q)) \to \Eb(\Fb_q)$

  Commits to a polynomial $p$ with degree bound $d$ where $d \geq d'$ using
  optional hiding $\o$.

- $\PCOpen(p: \Fb^{d'}_q[X], C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, \o: \Option(\Fb_q)) \to \EvalProof$

  Creates a proof, $\pi \in \EvalProof$, that the polynomial $p$, with
  commitment $C$, evaluated at $z$ gives $v = p(z)$, using the hiding input
  $\o$ if provided.

- $\PCCheck(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \EvalProof) \to \Result(\top, \bot)$

  Checks the proof $\pi$ that claims that the polynomial $p$ that $C$ is a
  commitment to, evaluates to $v = p(z)$.

Any given predicate $\Phi: X \to \Bb$ can be compiled into a circuit $R$. This
circuit can then be fed to the general-purpose proof scheme that further
compiles $X$ into a series of evaluation proofs $(\pi_1, \dots, \pi_n)$
that if they verify, convinces the verifier that $\Phi(X) = \top$

[^1]: Sonic Paper: [https://eprint.iacr.org/2019/099](https://eprint.iacr.org/2019/099)
[^2]: Plonk Paper: [https://eprint.iacr.org/2019/953](https://eprint.iacr.org/2019/953)
[^3]: Marlin Paper: [https://eprint.iacr.org/2019/1047](https://eprint.iacr.org/2019/1047)

### The Implementation

The authors also define a concrete Accumulation Scheme using the Discrete Log
assumption $\ASDL$, which uses the same algorithms as in the 2019 Halo
paper. This accumulation scheme in turn, relies heavily upon a Polynomial
Commitment Scheme, $\PCDL$, which is also described in the paper. Both of
these have been implemented as part of this project in Rust and the rest
of the document will go over these sets of algorithms, their security,
performance and implementation details.

Since these kinds of proofs can both be used for proving knowledge of a
large witness to a statement succinctly, and doing so without revealing
any information about the underlying witness, the zero-knowledgeness of the
protocol is described as _optional_. This is highlighted in the algorithmic
specifications as the parts colored \textblue{blue}. In the Rust
implementation I have chosen to include these parts as they were not too
cumbersome to implement, but since IVC is at the heart of this project,
not zero-knowledge, I have chosen to omit them from the soundness and
completeness discussions in the following sections as well as omitted the
proofs of zero-knowledgeness.

The authors of the paper present additional algorithms for setting up public
parameters ($\CMSetup$, $\PCDLSetup$, $\ASDLGenerator$) and distributing them
($\CMTrim$, $\PCDLTrim$, $\ASDLIndexer$), we omit them in the following
algorithmic specifications on the assumption that:

a. The setups has already been run, producing values $N, D \in \Nb, S, H \in_R
   \Eb(\Fb_q), \vec{G} \in_R \Eb(\Fb_q)$ where $D = N - 1$, $N$ is a
   power of two and any random values have been sampled honestly.
b. All algorithms have global access to the above values.

This more closely models the implementation where the values were
generated for a computationally viable value of $N$ and $S, H,
\vec{G}$ were randomly sampled using a hashing algorithm. More
specefically a genesis string was appended with an numeric index,
run through the sha3 hashing algorithm, then used to generate a curve
point. These values were then added as global constants in the code, see the
[`/code/src/consts.rs`](https://github.com/rasmus-kirk/halo-accumulation/blob/main/code/src/consts.rs)
in the repo.

The associated rust code for generating the public parameters can be seen below:

```rust {.numberLines}
// Function to generate a random generator for the Pallas Curve.
// Since the order of the curve is prime, any non-identity point is a generator.
fn get_generator_hash(i: usize) -> PallasPoint {
    let genesis_string = "To understand recursion, one must first understand recursion"
      .as_bytes();

    // Hash `genesis_string` concatinated with `i`
    let mut hasher = Sha3_256::new();
    hasher.update(genesis_string);
    hasher.update(i.to_le_bytes());
    let hash_result = hasher.finalize();

    // Interpret the hash as a scalar field element
    let scalar = PallasScalar::from_le_bytes_mod_order(&hash_result);

    // Generate a uniformly sampled point from the uniformly sampled field element
    PallasPoint::generator() * scalar
}

/// Get public parameters
fn get_pp(n: usize) -> (PallasPoint, PallasPoint, Vec<PallasPoint>) {
    let S = get_generator_hash(0);
    let H = get_generator_hash(1);
    let mut Gs = Vec::with_capacity(n);

    for i in 2..(n + 2) {
        Gs.push(get_generator_hash(i))
    }

    (S, H, Gs)
}
```

\newpage

# $\PCDL$: The Polynomial Commitment Scheme

## Outline

We have four main functions:

- $\PCDLCommit(p: \Fb^d_q[X], \o: \Option(\Fb_q)) \to \Eb(\Fb_q)$:

  Creates a commitment to the coefficients of the polynomial $q$ of degree
  $d$ with optional hiding $\o$, using pedersen commitments.

- $\PCDLOpen(p: \Fb^d_q[X], C: \Eb(\Fb_q), z: \Fb_q, \o: \Option(\Fb_q)) \to \EvalProof$:

  Creates a proof $\pi$ that states: "I know $p \in \Fb^d_q[X]$ with
  commitment $C \in \Eb(\Fb_q)$ s.t. $p(z) = v$" where $p$ is private
  and $d, z, v$ are public.

- $\PCDLSuccinctCheck(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \EvalProof) \to \Result((\Fb^d_q[X], \Gb), \bot)$:

  Cheaply checks that a proof $\pi$ is correct. It is not a full check however,
  since an expensive part of the check is deferred until a later point.

- $\PCDLCheck(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \EvalProof) \to \Result(\top, \bot)$:

  The full check on $\pi$.

The following subsections will describe them in pseudo-code.

### $\PCDLCommit$

\begin{algorithm}[H]
\caption{$\PCDLCommit$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$p: \Fb^d_q[X]$}{The univariate polynomial that we wish to commit to.} \\
  \Desc{$\mathblue{\o}: \Option(\Fb_q)$}{Optional hiding factor for the commitment.} \\
\textbf{Output} \\
  \Desc{$C: \Eb(\Fb_q)$}{The pedersen commitment to the coefficients of polynomial $p$.}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1)$ is a power of 2.
  \State Let $\vec{p}$ be the coefficient vector for $p$
  \State Output $C := \CMCommit(\vec{G}, \vec{p}, \mathblue{\o})$.
\end{algorithmic}
\end{algorithm}

$\PCDLCommit$ is rather simple, we just take the coefficients of the polynomial and
commit to them using a pedersen commitment.

### $\PCDLOpen$

\begin{algorithm}[H]
\caption{$\PCDLOpen$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$p: \Fb^d_q[X]$}{The univariate polynomial that we wish to open for.} \\
  \Desc{$C: \Eb(\Fb_q$)}{A commitment to the coefficients of $p$.} \\
  \Desc{$z: \Fb_q$}{The element that $z$ will be evaluated on $v = p(z)$.} \\
  \Desc{$\mathblue{\o}: \Option(\Fb_q)$}{Optional hiding factor for $C$. \textit{Must} be included if $C$ was created with hiding!} \\
\textbf{Output} \\
  \Desc{$\EvalProof$}{Proof that states: "I know $p \in \Fb^d_q[X]$ with commitment $C \in \Eb(\Fb_q)$ s.t. $p(z) = v$"}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1)$ is a power of 2.
  \State Compute $v = p(z)$ and let $n = d+1$.
  \State \textblue{Sample a random polynomial $\bar{p} \in \Fb^{\leq d}_q[X]$ such that $\bar{p}(z) = 0$}.
  \State \textblue{Sample corresponding commitment randomness $\bar{\o} \in \Fb_q$.}
  \State \textblue{Compute a hiding commitment to $\bar{p}$: $\bar{C} \gets \CMCommit(\vec{G}, \bar{p}, \bar{\o}) \in \Gb$.}
  \State \textblue{Compute the challenge $\a := \rho_0(C, z, v, \bar{C}) \in \Fb^{*}_q$.}
  \State \textblue{Compute commitment randomness $\o' := \o + \a \bar{\o} \in \Fb_q$}.
  \State Compute the polynomial $p' := p \mathblue{+ \a \bar{p}} = \sum_{i=0} c_i X_i \in \Fb_q[X]$.
  \State Compute a non-hiding commitment to $p'$: $C' := C \mathblue{+ \a \bar{C} - \o' S} \in \Gb$.
  \State Compute the 0-th challenge field element $\xi_0 := \rho_0(C', z, v) \in \Fb_q$, then $H' := \xi_0 H \in \Gb$.
  \State Initialize the vectors ($\vec{c_0}$ is defined to be coefficient vector of $p'$):
    \Statex \algind $
      \begin{alignedat}[b]{1}
        \vec{c_0} &:= (c_0, c_1, \dots, c_d) \in F^n_q \\ 
        \vec{z_0} &:= (1, z^1, \dots, z^d) \in F^n_q \\
        \vec{G_0} &:= (G_0, G_1, \dots, G_d) \in \Gb_n \\
      \end{alignedat}
    $
  \For{$i \in [\lg(n)]$}
    \State Compute $L_i := \CMCommit(l(\vec{G_{i-1}}) \cat H', \; \;  r(\vec{c_{i-1}}) \cat \langle r(\vec{c_{i-1}}), l(\vec{z_{i-1}}) \rangle, \; \; \bot)$
    \State Compute $R_i := \CMCommit(r(\vec{G_{i-1}}) \cat H', \; \; l(\vec{c_{i-1}}) \cat \langle l(\vec{c_{i-1}}), r(\vec{z_{i-1}}) \rangle, \; \; \bot)$
    \State Generate the i-th challenge $\xi_i := \rho_0(\xi_{i-1}, L_i, R_i) \in \Fb_q$.
    \State Construct commitment inputs for the next round: 
      \Statex \algindd $
        \begin{alignedat}[b]{3}
          \vec{G_i} &:= l(\vec{G_{i-1}}) &&+ \xi_i      &&\cdot r(\vec{G_{i-1}}) \\ 
          \vec{c_i} &:= l(\vec{c_{i-1}}) &&+ \xi^{-1}_i &&\cdot r(\vec{c_{i-1}}) \\
          \vec{z_i} &:= l(\vec{z_{i-1}}) &&+ \xi_i      &&\cdot r(\vec{z_{i-1}}) \\
        \end{alignedat}
      $
  \EndFor
  \State Finally output the evaluation proof $\pi := (\vec{L},\vec{R}, U := G^{(0)}, c := c^{(0)}, \mathblue{\bar{C}, \o'})$
\end{algorithmic}
\end{algorithm}

The $\PCDLOpen$ algorithm mostly follows the IPA algorithm from
Bulletproofs. Except,in this case we are trying to prove we know polynomial
$p$ s.t. $v = \dotp{\vec{c_0}}{\vec{z_0}}$. So because $z$ is public, we
can get away with omitting the generators, $(\vec{H})$, for $\vec{b}$ which
we would otherwise need in the Bulletproofs IPA. For efficiency we also
send along the curve point $U = G^{(0)}$, which the original IPA does not
do. The $\PCDLSuccinctCheck$ uses this to make its check and $\PCDLCheck$
verifies its correctness.

### $\PCDLSuccinctCheck$

\begin{algorithm}[H]
\caption{$\PCDLSuccinctCheck$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$C: \Eb(\Fb_q)$}{A commitment to the coefficients of $p$.} \\
  \Desc{$d: \Nb$}{The degree of $p$} \\
  \Desc{$z: \Fb_q$}{The element that $p$ is evaluated on.} \\
  \Desc{$v: \Fb_q$}{The claimed element $v = p(z)$.} \\
  \Desc{$\pi: \EvalProof$}{The evaluation proof produced by $\PCDLOpen$} \\
\textbf{Output} \\
  \Desc{$\Result((\Fb^d_q[X], \Gb), \bot)$}{
    The algorithm will either succeed and output ($h: \Fb^d_q[X], U: \Gb$) if $\pi$ is a valid proof and otherwise fail ($\bot$).
  }
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1)$ is a power of 2.
  \State Parse $\pi$ as $(\vec{L},\vec{R}, U := G^{(0)}, c := c^{(0)}, \mathblue{\bar{C}, \o'})$ and let $n = d + 1$.
  \State \textblue{Compute the challenge $\alpha := \rho_0(C, z, v, \bar{C}) \in F^{*}_q$.}
  \State Compute the non-hiding commitment $C' := C \mathblue{+ \a \bar{C} - \o'S} \in \Gb$.
  \State Compute the 0-th challenge: $\xi_0 := \rho_0(C', z, v)$, and set $H' := \xi_0 H \in \Gb$.
  \State Compute the group element $C_0 := C' + vH' \in \Gb$.
  \For{$i \in [\lg(n)]$}
    \State Generate the i-th challenge: $\xi_i := \rho_0(\xi_{i-1}, L_i, R_i) \in \Fb_q$.
    \State Compute the i-th commitment: $C_i := \xi^{-1}_i L_i + C_{i-1} + \xi_i R_i \in \Gb$.
  \EndFor
\State Define the univariate polynomial $h(X) := \prod^{\lg(n)-1}_{i=0} (1 + \xi_{\lg(n) - i} X^{2^i}) \in \Fb_q[X]$.
\State Compute the evaluation $v' := c \cdot h(z) \in \Fb_q$.
\State Check that $C_{lg(n)} \meq cU + v'H'$
\State Output (h(X), U).
\end{algorithmic}
\end{algorithm}

### $\PCDLCheck$

\begin{algorithm}[H]
\caption{$\PCDLCheck$}\label{alg:pcdl_check}
\textbf{Inputs} \\
  \Desc{$C: \Eb(\Fb_q)$}{A commitment to the coefficients of $p$.} \\
  \Desc{$d: \Nb$}{The degree of $p$} \\
  \Desc{$z: \Fb_q$}{The element that $p$ is evaluated on.} \\
  \Desc{$v: \Fb_q$}{The claimed element $v = p(z)$.} \\
  \Desc{$\pi: \EvalProof$}{The evaluation proof produced by $\PCDLOpen$} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{The algorithm will either succeed ($\top$) if $\pi$ is a valid proof and otherwise fail ($\bot$).}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1)$ is a power of 2.
  \State Check that $\PCDLSuccinctCheck(C, d, z, v, \pi)$ accepts and outputs $(h, U)$.
  \State Check that $U \meq \CMCommit(\vec{G}, \vec{h}, \bot)$, where $\vec{h}$ is the coefficient vector of the polynomial $h$.
\end{algorithmic}
\end{algorithm}

## Completeness

### Check 1 in $\PCDLSuccinctCheck$: $C_{lg(n)} \meq cU + v'H'$

Let's start by looking at $C_{lg(n)}$. The verifer computes $C_{lg(n)}$ as:

$$
\begin{aligned}
  C_0        &= C' + vH' = C + vH' \\
  C_{\lg(n)} &= C_0 + \sum^{\lg(n)-1}_{i=0} \xi^{-1}_{i+1} L_i + \xi_{i+1} R_i \\
\end{aligned}
$$

Given that the prover is honest, the following invariant should hold:

$$
\begin{alignedat}[b]{1}
  C_{i+1} &= \ip{\vec{c}_{i+1}}{\vec{G}_{i+1}} + \ip{\vec{c}_{i+1}}{\vec{z}_{i+1}} H'\\ 
          &= \ip{l(\vec{c}_i) + \xi^{-1}_{i+1} r(\vec{c}_i)}{l(\vec{G}_i) + \xi_{i+1} r(\vec{G}_i)} 
            + \ip{l(\vec{c}_i) + \xi^{-1}_{i+1} r(\vec{c}_i)}{l(\vec{z}_i) + \xi_{i+1} r(\vec{z}_i)} H'\\
          &= \ip{l(\vec{c}_i)}{l(\vec{G}_i)} + \xi_{i+1} \ip{l(\vec{c}_i))}{r(\vec{G}_i}
            + \xi^{-1}_{i+1} \ip{r(\vec{c}_i)}{l(\vec{G}_i)} + \ip{r(\vec{c}_i)}{r(\vec{G}_i)}\\
          &+ (\ip{l(\vec{c}_i)}{l(\vec{z}_i)} + \xi_{i+1} \ip{l(\vec{c}_i)}{r(\vec{z}_i)} 
            + \xi^{-1}_{i+1} \ip{r(\vec{c}_i)}{l(\vec{z}_i)} + \ip{r(\vec{c}_i)}{l(\vec{z}_i)}) H'
\end{alignedat}
$$

If we group these terms:

$$
\begin{alignedat}[b]{4}
  C_{i+1} &= \ip{l(\vec{c}_i)}{l(\vec{z}_i)}  &&+ \ip{r(\vec{c}_i)}{r(\vec{G}_i)}     &&+ \xi_{i+1} \ip{l(\vec{c}_i)}{r(\vec{G}_i)}    &&+ \xi^{-1}_{i+1} \ip{r(\vec{c}_i)}{l(\vec{G}_i)} \\
          &+ (\ip{l(\vec{c}_i)}{l(\vec{z}_i)} &&+ \ip{r(\vec{c}_i)}{r(\vec{z}_i)}) H' &&+ \xi_{i+1} \ip{l(\vec{c}_i)}{r(\vec{z}_i)} H' &&+ \xi^{-1}_{i+1} \ip{r(\vec{c}_i)}{l(\vec{z}_i)} H' \\
          &= C_i                              &&                                      &&+ \xi_{i+1} R_i                                &&+ \xi^{-1}_{i+1} L_i \\
          &\mkern-18mu\mkern-18mu \textbf{Where:} && && && \\
  L_i     &= \ip{r(\vec{c}_i)}{l(\vec{G}_i)} &&+ \ip{r(\vec{c}_i)}{l(\vec{z}_i)} H' && && \\
  R_i     &= \ip{l(\vec{c}_i)}{r(\vec{G}_i)} &&+ \ip{l(\vec{c}_i)}{r(\vec{z}_i)} H' && && 
\end{alignedat}
$$

We see why $\vec{L}, \vec{R}$ is defined the way they are. They help
the verifier check that the original relation hold, by showing it for the
compressed form $C_{i+1}$. $\vec{L}, \vec{R}$ is just the minimal information
needed to communicate this fact.

This leaves us with the following vectors (notice the slight difference in length):

$$
\begin{alignedat}[b]{1}
  \vec{L}    &= (L_1, \dots, L_{\lg(n)}) \\
  \vec{R}    &= (R_1, \dots, R_{\lg(n)}) \\
  \vec{C}    &= (C_0, \dots, C_{\lg(n)}) \\
  \vec{\xi}  &= (\xi_0, \dots, \xi_{\lg(n)}) \\
\end{alignedat}
$$

This means an honest prover will indeed produce $\vec{L}, \vec{R}$ s.t. $C_{\lg(n)} = C_0 + \sum^{\lg(n)-1}_{i=0} \xi^{-1}_{i+1} L_i + \xi_{i+1} R_i$

Let's finally look at the left-hand side of the verifying check:

\begin{align*}
  C_{\lg(n)} &= C_0 + \sum^{\lg(n)-1}_{i=0} \xi^{-1}_{i+1} L_i + \xi_{i+1} R_i && \\
             \intertext{The original definition of $C_i$:}
             &= \ip{\vec{c}_{\lg(n)}}{\vec{G}_{\lg(n)}} + \ip{\vec{c}_{\lg(n)}}{\vec{z}_{\lg(n)}} H' \\
             \intertext{Vectors have length one, so we use the single elements $c^{(0)}, G^{(0)}, c^{(0)}, z^{(0)}$ of the vectors:}
             &= c^{(0)}G^{(0)} + c^{(0)}z^{(0)} H'                                                   \\
             \intertext{The verifier has $c^{(0)} = c, G^{(0)} = U$ from $\pi \in \EvalProof$:}
             &= cU + cz^{(0)} H'                                                                     \\
             \intertext{Then, by construction of $h(X) \in \Fb^d_q[X]$}
             &= cU + ch(z) H'                                                                        \\
             \intertext{Finally we use the definition of $v'$:}
             &= cU + v'H'                                                                            \\
\end{align*}
Which corresponds exactly to the check that the verifier makes.

### Check 2 in $\PCDLCheck$: $U \meq \CMCommit(\vec{G}, \vec{h}, \bot)$

The honest prover will define $U = G^{(0)}$ as promised and the right-hand
side will also become $U = G^{(0)}$ by the construction of $h(X)$. Adding
hiding has no effect on this check.

## Soundness

## Benchmarks

# $\ASDL$: The Accumulation Scheme

## Outline

### $\ASDLCommonSubroutine$

\begin{algorithm}[H]
\caption{$\ASDLCommonSubroutine$}
\textbf{Inputs} \\
  \Desc{$d: \Nb$}{The degree of $p$.} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
  \Desc{$\mathblue{\pi_V}: \Option(\AccHiding)$}{Necessary parameters if hiding is desired.} \\
\textbf{Output} \\
  \Desc{$\Result((\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X]), \bot)$}{
    The algorithm will either succeed $(\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X])$
    if the instances has consistent degree and hiding parameters and otherwise
    fail ($\bot$).
  }
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State \textblue{Parse $\pi_V$ as $(h_0, U_0, \o)$, where $h_0(X) = aX + b \in \Fb^1_q[X], U_0 \in \Gb$ and $\o \in \Fb_q$}
  \State \textblue{Check that $U_0$ is a deterministic commitment to $h_0$: $U_0 = \PCDLCommit(h, \bot)$.}
  \For{$i \in [m]$}
    \State Parse $q_i$ as a tuple $((C_i, d_i, z_i, v_i), \pi_i)$.
    \State Compute $(h_i(X), U_i) := \PCDLSuccinctCheck(C_i, z_i, v_i, \pi_i)$.
    \State Check that $d_i \leq d$
  \EndFor
  \State Compute the challenge $\a := \rho_1(\vec{h}, \vec{U}) \in \Fb_q$
  \State Let the polynomial $h(X) := \mathblue{h_0 +} \sum^m_{i=1} \a^i h_i \in \Fb_q[X]$
  \State Compute the accumulated commitment $C := \mathblue{U_0 +} \sum^m_{i=1} \a^i U_i$
  \State Compute the challenge $z := \rho_1(C, h) \in \Fb_q$.
  \State Randomize $C$: $\bar{C} := C \mathblue{+ \o S} \in \Gb$.
  \State Output $(\bar{C}, d, z, h(X))$.
\end{algorithmic}
\end{algorithm}

### $\ASDLProver$

\begin{algorithm}[H]
\caption{$\ASDLProver$}
\textbf{Inputs} \\
  \Desc{$d: \Nb$}{The degree of $p$.} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
\textbf{Output} \\
  \Desc{$\Result(\Acc, \bot)$}{
    The algorithm will either succeed $((\bar{C}, d, z, v, \pi), \pi_V)
    \in \Acc)$ if the instances has consistent degree and hiding
    parameters and otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State \textblue{Sample a random linear polynomial $h_0 \in F_q[X]$}
  \State \textblue{Then compute a deterministic commitment to $h_0$: $U_0 := \PCDLCommit(h_0, \bot)$}
  \State \textblue{Sample commitment randomness $\o \in F_q$, and set $\pi_V := (h_0, U_0, \o)$.}
  \State Then, compute the tuple $(\bar{C}, d, z, h(X)) := \ASDLCommonSubroutine(d, \vec{q} \mathblue{, \pi_V})$.
  \State Compute the evaluation $v := h(z)$
  \State Generate the hiding evaluation proof $\pi := \PCDLOpen(h(X), \bar{C}, d, z \mathblue{, \o})$.
  \State Finally, output the accumulator $acc = \mathblue{(}(\bar{C}, d, z, v, \pi)\mathblue{, \pi_V)}$.
\end{algorithmic}
\end{algorithm}

### $\ASDLVerifier$

\begin{algorithm}[H]
\caption{$\ASDLVerifier$}
\textbf{Inputs} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
  \Desc{$acc: \Acc$}{The accumulator.} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{
    The algorithm will either succeed $(\top)$ if $acc$ correctly accumulates
    $\vec{q}$ and otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $acc.d \leq D$
  \Require $(acc.d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $acc$ as $\mathblue{(}(\bar{C}, d, z, v, \_)\mathblue{, \pi_V)}$
    \State The accumulation verifier computes $(\bar{C}', d', z', h(X)) := \ASDLCommonSubroutine(d, \vec{q} \mathblue{, \pi_V})$
    \State Then checks that $\bar{C}' \meq \bar{C}, d' \meq d, z' \meq z$, and $h(z) \meq v$.
\end{algorithmic}
\end{algorithm}

### $\ASDLDecider$

\begin{algorithm}[H]
\caption{$\ASDLDecider$}
\textbf{Inputs} \\
  \Desc{$acc: \Acc$}{The accumulator.} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{
    The algorithm will either succeed $(\top)$ if the accumulator has correctly
    accumulated all previous instances and will otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $acc.d \leq D$
  \Require $(acc.d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $acc$ as $((\bar{C}, d, z, v, \pi), \_)$
    \State Check $\top \meq \PCDLCheck(\bar{C}, d, z, v, \pi)$
\end{algorithmic}
\end{algorithm}

## Completeness

$\ASDLVerifier$ runs the same algorithm ($\ASDLCommonSubroutine$) with the
same inputs and, given that $\ASDLProver$ is honest, will therefore get
the same outputs, these outputs are checked and therefore $\ASDLVerifier$
will always accept, returning $\top$.

As for the $\ASDLDecider$, it just runs $\PCDLCheck$, since we know that
$\PCDL$ is sound the honest $\ASDLProver$ constructed $\pi$ correctly,
we know that this check too will always pass.

**TODO**: Maybe explain why $\bar{C}, d, z, v, \o$ are valid

## Soundness

## Benchmarks

\newpage

# Appendix

## Notation

|                                                                                 |                                                                                                           |
|:--------------------------------------------------------------------------------|:----------------------------------------------------------------------------------------------------------|
| $[n]$                                                                           | Denotes the integers $\{ 1, ..., n \}$                                                                    |
| $a \in \Fb_q$                                                                   | A field element in a prime field of order $q$                                                             |
| $\vec{a} \in S^n_q$                                                             | A vector of length $n$ consisting of elements from set $S$                                                |
| $G \in \Eb(\Fb_q)$                                                              | An elliptic Curve point, defined over field $\Fb_q$                                                       |
| $\vec{G}$                                                                       | A vector                                                                                                  |
| $v^{(0)}$                                                                       | The singular element of a fully compressed vector $\vec{v_{\lg(n)}}$ from $\PCDLOpen$.                    |
| $a \in_R S$                                                                     | $a$ is a uniformly randomly sampled element of $S$                                                        |
| $(S_1, \dots, S_n)$                                                             | In the context of sets, the same as $S_1 \times \dots \times S_n$                                         |
| $\dotp{\vec{a}}{\vec{G}}$ where $\vec{a} \in \Fb^n_q, \vec{G} \in \Eb^n(\Fb_q)$ | The dot product of $\vec{a}$ and $\vec{G}$ ($\sum^n_{i=0} a_i G_i$).                                      |
| $\dotp{\vec{a}}{\vec{b}}$ where $\vec{a} \in \Fb^n_q, \vec{b} \in \Fb^n_q$      | The dot product of vectors $\vec{a}$ and $\vec{b}$.                                                       |
| $l(\vec{a})$                                                                    | Gets the left half of $\vec{a}$.                                                                          |
| $r(\vec{a})$                                                                    | Gets the right half of $\vec{a}$.                                                                         |
| $\vec{a} \cat \vec{b}$ where $\vec{a} \in \Fb^n_q, \vec{b} \in \Fb^m_q$         | Concatinate vectors to create $\vec{c} \in \Fb^{n+m}_q$.                                                  |
| $a \cat b$ where $a \in \Fb_q$                                                  | Create vector $\vec{c} = (a, b)$.                                                                         |
| $\Bb$                                                                           | Represents a boolean $\{ \top, \bot \}$                                                                   |
| $\Option(T)$                                                                    | $\{ T, \bot \}$                                                                                           |
| $\Result(T, E)$                                                                 | $\{ T, E \}$                                                                                              |
| $\EvalProof$                                                                    | $(\Eb^{lg(n)}(\Fb_q), \Eb^{lg(n)}(\Fb_q), \Eb(\Fb_q), \Fb_q\mathblue{, \Eb(\Fb_q), \Fb_q})$               |
| $\AccHiding$                                                                    | $(\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q)$                                                                       |
| $\Acc$                                                                          | $((\Eb(\Fb_q), \Nb, \Fb_q, \Fb_q, \EvalProof), \AccHiding)$                                               |

Note that the following are isomorphic $\Bb \iso \Option(\top) \iso
\Result(\top, \bot)$, but they have different connotations.

## $\mathrm{CM}$: Pedersen Commitment

As a reference, we include the Pedersen Commitment algorithm we use:

\begin{algorithm}[H]
\caption{$\CMCommit$}
\textbf{Inputs} \\
  \Desc{$\vec{m}: \Fb^n$}{The vectors we wish to commit to.} \\
  \Desc{$\vec{G}: \Eb(\Fb)^n$}{The generators we use to create the commitment.} \\
  \Desc{$\mathblue{\o}: \Option(\Fb_q)$}{Optional hiding factor for the commitment.} \\
\textbf{Output} \\
  \Desc{$C: \Eb(\Fb_q)$}{The pedersen commitment.}
\begin{algorithmic}[1]
  \State Output $C := \ip{\vec{m}}{\vec{G}} \mathblue{+ \o S}$.
\end{algorithmic}
\end{algorithm}

```rust {.numberLines}
pub fn commit(
  w: Option<&PallasScalar>,
  Gs: &[PallasAffine],
  ms: &[PallasScalar]) -> PallasPoint
{
    assert!(Gs.len() == ms.len());

    let acc = point_dot_affine(ms, Gs);
    if let Some(w) = w {
        S * w + acc
    } else {
        acc
    }
}
```
