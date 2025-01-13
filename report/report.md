---
title: Investigating IVC with Halo2
date: \today
author: 
  - Rasmus Kirk Jakobsen - 201907084
geometry: margin=2cm
---

<!-- TODO: FRI does not technically form a PCS, but it's comparable -->

\tableofcontents
\newpage

# Introduction

Halo2, can be broken down into the following components:

- **Plonk**: A general-purpose, potentially zero-knowledge, proof scheme.
- **$\PCDL$**: A Polynomial Commitment Scheme in the Discrete Log setting.
- **$\ASDL$**: An Accumulation Scheme in the Discrete Log setting.
- **Pasta**: A Cycle of Elliptic Curves, namely **Pa**llas and Ve**sta**.

This project is focused on the components of $\PCDL$ and $\ASDL$. I used the
[2020 paper](https://eprint.iacr.org/2020/499.pdf) _"Proof-Carrying Data from Accumulation
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
Verifier, V. The Prover tries to convince the Verifier of a statement
$x \in L$ language $L$ in NP. The following properties must be true:

- Completeness: $\forall P \in ITM, x\in L \implies Pr[V_{out} = \bot] \leq \epsilon(x)$

  For all honest provers, P, where $x$ is true, the probability that the
  verifier remains unconvinced is negligible in the length of $x$.

- Soundness: $\forall P^* \in ITM, x \notin L \implies Pr[V_{out} = \top] \leq \epsilon(x)$

  For all provers, honest or otherwise, $P^*$, that tries to convince the
  verifier of a claim, $x$, that is not true, the probability that the
  verifier will be convinced is negligible in the length of $x$.

An Interactive Argument is very similar, but the honest and malicious prover
is now polynomially bounded and receives a witness, $w$:

- Completeness: $\forall P(w) \in PPT, x\in L \implies Pr[V_{out} = \bot] \leq \epsilon(x)$
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
  an efficient extractor $E$, that when given a possibly malicious prover $P^*$
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
denotes the transcript between the honest prover and (possibly) malicious verifier. There are three kinds
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
cryptocurrencies. They usually also function as so-called general-purpose
proof schemes. This means that, given any solution to an NP-problem, it will
produce a proof that the prover knows the solution to said NP-problem. Most
SNARKs also allow for zero-knowledge arguments, making them zk-SNARKs.

More concretely, imagine that Alice has todays sudoku problem $x$: She
claims to have a solution to this problem, her witness, $w$, and want to
convince Bob without having to send all of it. She could then use a SNARK to
create a proof to convince Bob. To do this she must first encode the sudoku
verifier as a circuit $R_x$, which includes public inputs, such as today's
sudoku values/positions, etc, and then give the SNARK prover ($\SNARKProver$)
$R_x(w,w')$. Finally she can send this proof, $\pi$, to Bob along with the
public sudoku verifying circuit, $R_x$, and he can check the proof and be
convinced using the snark verifier ($\SNARKVerifier$).

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
without taking the time to redo all that computation? In order to do this,
the verification of the final output of the computation must be much smaller
than simply running the computation again. Valiant creates the concepts of
IVC and argues that IVC can be used to acheive the above goal.

Recently the concept of IVC has seen renewed interest with cryptocurrencies,
as this concept lends itself well to the structure of blockchains. This
allows a blockchain node to omit all previous transaction history in
favour of only a single state, for example, containing all current account
balances. This is commonly called a _succinct blockchain_, one such blockchain
is [Mina](https://minaprotocol.com/).

In order to acheive IVC, you need a function $F(x) \in S \to S$ along with some
initial state $s_0 \in S$. Then you can call $F(x)$ to generate a series of
$s$'s, $\vec{s} \in S^{n+1}$:

\begin{figure}[!H]
\centering
\begin{tikzpicture}[node distance=2cm]

  % Nodes
  \node (s0) [node] {$s_0$};
  \node (s1) [node, right=of s0] {$s_1$};
  \node (s2) [node, right=of s1] {$s_2$};
  \node (dots) [right=2cm of s2] {$\dots$};
  \node (sn) [node, right=2cm of dots] {$s_n$};

  % Arrows with labels
  \draw[arrow] (s0) -- node[above] {$F(s_0)$} (s1);
  \draw[arrow] (s1) -- node[above] {$F(s_1)$} (s2);
  \draw[arrow] (s2) -- node[above] {$F(s_2)$} (dots);
  \draw[arrow] (dots) -- node[above] {$F(s_{n-1})$} (sn);

\end{tikzpicture}
\caption{
  A visualisation of the relationship between $F(x)$ and $\vec{s}$ in a non-IVC setting.
}
\end{figure}

In a blockchain setting, you might imagine any $s_i \in \vec{s}$
as a set of accounts with corresponding balances, and the transition
function[^ivc-blockchain] $F(x)$ as the computation happening when a new
block is created and therefore a new state $s_i$. In the IVC setting, we
have a proof, $\pi$, associated with each state, so that anyone can take
just a single pair $(s_m, \pi_m)$ along with the initial state and transition
function ($s_0, F(x)$) and verify that said state was computed correctly.

\begin{figure}[!H]
\centering
\begin{tikzpicture}[node distance=2cm]

  % Nodes
  \node (s0) [node] {$s_0$};
  \node (s1) [node, right=of s0] {$(s_1, \pi_1)$};
  \node (dots) [right=2cm of s1] {$\dots$};
  \node (sn) [node, right=3cm of dots] {$(s_n, \pi_n)$};

  % Arrows with labels
  \draw[arrow] (s0) -- node[above] {$\Pc(s_0, \bot)$} (s1);
  \draw[arrow] (s1) -- node[above] {$\Pc(s_1, \pi_1)$} (dots);
  \draw[arrow] (dots) -- node[above] {$\Pc(s_{n-1}, \pi_{n-1})$} (sn);

\end{tikzpicture}
\caption{
  A visualization of the relationship between $F, \vec{s}$ and $\vec{\pi}$
  in an IVC setting using traditional SNARKs. $\Pc(s_i, \pi_i)$ denotes
  $\SNARKProver(s_{i-1}, R_F, \pi_{i-1}) = (s_i, \pi_i)$.
}
\end{figure}

The proof $\pi_i$ describes the following claim:

> _\textcolor{GbFg3}{"The current state $s_i$ is computed from applying the function, $F$, $i$ times to $s_0$
> ($s_i = F^i(s_0) = F(s_{i-1})$) and the associated proof $\pi_{i-1}$ for
> the previous state is valid."}_

Or more formally, $\pi_i$ is a proof of the following claim, expressed as
a circuit $R$:

$$R := \text{I.K.} \; \pi_{n-1} \; \text{ s.t. } \; s_i \meq F(s_{i-1}) \; \land \; (s_{i-1} \meq s_0 \lor \SNARKVerifier(R, s_{i-1}, \pi_{i-1}) \meq \top))$$

Note that $s_{i-1}, s_0$ are not quantified above, but are public values. The
$\SNARKVerifier$ represents the verification circuit in the proof system
we're using. This means, that we're taking the verifier, representing it as
a circuit, and then feeding it to the prover. This is not a trivial task
in practice! It also means that the verification time must be sublinear
to acheive an IVC scheme, otherwise the verifier could just have computed
$F^{n+1}(s_0)$ themselves, as $s_0$ and $F(x)$ necessarily must be public.

To see that the above construction works, observe that $\pi_1, \dots, \pi_n$ proves:

$$
\begin{alignedat}{7}
  &\text{I.K.} \; \pi_{n-1} \; &&\text{ s.t. } \; &&s_n     &&= F(s_{n-1}) \; &&\land \; (s_{n-1} = s_0  &&\lor \SNARKVerifier(R, s_{n-1}, \pi_{n-1}) = \top), \\
  &\text{I.K.} \; \pi_{n-2} \; &&\text{ s.t. } \; &&s_{n-1} &&= F(s_{n-2}) \; &&\land \; (s_{n-2} = s_0  &&\lor \SNARKVerifier(R, s_{n-2}, \pi_{n-2}) = \top), \; \dots \\
  &                            &&              \; &&s_1     &&= F(s_0)     \; &&\land \; (s_0 = s_0      &&\lor \SNARKVerifier(R, s_0, \pi_0) = \top)
\end{alignedat}
$$

Which means that:

$$
\begin{alignedat}{4}
  &\SNARKVerifier(R, s_n, \pi_n) = \top \implies \\
  &s_n = F(s_{n-1}) \; \land \; \\
  &\SNARKVerifier(R, s_{n-1}, \pi_{n-1}) = \top \; \land \; \\
  &s_{n-1} = F(s_{n-2}) \implies \dots \\
  &\SNARKVerifier(R, s_1 \pi_1) = \top \implies \\
  &s_1 = F(s_0)
\end{alignedat}
$$

Thus, by induction $s_n = F^n(s_0)$

[^ivc-blockchain]: In the blockchain setting, the transition function would also take an additional input representing new transactions, $F(x: S, T: \Pc(T))$ 

### Bulletproofs

In 2017, [the Bulletproofs paper](https://eprint.iacr.org/2017/1066.pdf)
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
times. Unfortunately, the IPA, and by extension Bulletproofs, suffer
from linear verification time, making them unsuitible for IVC.

### Polynomial Commitment Schemes

In the section SNARKs section, general-purpose proof schemes were
described. Modern general-purpose (zero-knowledge) proof schemes, such as
Sonic[^1], Plonk[^2] and Marlin[^3], commonly use _Polynomial Commitment
Schemes_ (PCSs) for creating their proofs. This means that different PCSs
can be used to get security under weaker or stronger assumptions.

- **KZG PCSs:** Uses a trusted setup, this would give you a traditional SNARK.
- **Bulletproofs PCSs:** Uses an untrusted setup, assumes secure if the Discrete Log problem is hard, the verifier is linear.
- **FRI PCSs:** Also uses an untrusted setup, assumes secure one way functions
  exist. It has a higher overhead than PCSs based on the Discrete Log
  assumption, but since it's not based on the Discrete Log assumption, and
  instead assumes that secure one-way functions exist, you end up with a
  quantum secure PCS.

A PCS allows a prover to prove to a verifier that a commited polynomial
evaluates to a certain value, $v$, given an evaluation input $z$.There are
three main functions used to prove this ($\PCSetup$ and $\PCTrim$ omitted):

- $\PCCommit(p: \Fb^{d'}_q[X], d: \Nb, \o: \Option(\Fb_q)) \to \Eb(\Fb_q)$

  Commits to a degree-$d'$ polynomial $p$ with degree bound $d$ where $d'
  \leq d$ using optional hiding $\o$.

- $\PCOpen(p: \Fb^{d'}_q[X], C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, \o: \Option(\Fb_q)) \to \EvalProof$

  Creates a proof, $\pi \in \EvalProof$, that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' \leq d$, evaluated at
  $z$ gives $v = p(z)$, using the hiding input $\o$ if provided.

- $\PCCheck(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \EvalProof) \to \Result(\top, \bot)$

  Checks the proof $\pi$ that claims that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' \leq d$, evaluates to
  $v = p(z)$.

Any NP-problem, $X \in NP$, with a witness $w$ can be compiled into a circuit
$R_X$. This circuit can then be fed to a general-purpose proof scheme prover
$\Pc_{R_X}$ along with the witness $w \in X$, that creates a proof of the
statement $"R_X(w) = \top"$, typically consisting of a series of pairs
representing opening proofs:

$$(q_1 = (C_1, d, z_1, v_1, \pi_1), \dots, q_m = (C_m, d, z_m, v_m, \pi_m))$$

These pairs can more generally be referred as _instances_. They can then be
verified using $\PCCheck$:

$$\PCCheck(C_1, d, z_1, v_1, \pi_1) \meq \dots \meq \PCCheck(C_m, d, z_m, v_m, \pi_m) \meq \top$$

Along with some checks that the evaluations $\vec{v}$ satisfies any desired
relations associated with the circuit $R_X$, which we can model using a
function $I_X \in \Instance \to \{ \top, \bot \}$. If all these checks verify,
then the verifier $\Vc_X$ will be convinced that $w$ is a valid witness for
$X$. In this way, a proof of knowledge of a witness for any NP-problem can
be represented as a series of PCS evaluation proofs, including our desired
witness that $s_n = F^n(s_0)$.

[^1]: Sonic Paper: [https://eprint.iacr.org/2019/099](https://eprint.iacr.org/2019/099)
[^2]: Plonk Paper: [https://eprint.iacr.org/2019/953](https://eprint.iacr.org/2019/953)
[^3]: Marlin Paper: [https://eprint.iacr.org/2019/1047](https://eprint.iacr.org/2019/1047)

### Accumulation Schemes

The authors of [a 2019 paper](https://eprint.iacr.org/2019/1021.pdf) presented
_Halo,_ the first practical example of recursive proof composition without
a trusted setup. Using a modified version of the Bulletproofs-style Inner
Product Argument (IPA), they present a polynomial commitment scheme. Computing
the evaluation of a point $z \in \Fb_q$ on polynomial $p(X) \in \Fb^d_q[X]$
as $v = \ip{\vec{p}}{\vec{z}}$ where $\vec{z} = (z^0, z^1, \dots, z^{d})$
and $\vec{p} \in \Fb^{d+1}$ is the coefficient vector of $p(X)$, using
the IPA. However, since the the vector $\vec{z}$ is not private, and has a
certain structure, we can split the verification algorithm in two: A sublinear
$\PCDLSuccinctCheck$ and linear $\PCDLCheck$. Using the $\PCDLSuccinctCheck$
we can accumulate $n$ instances, and only perform the expensive linear check
(i.e. $\PCDLCheck$) at the end of accumulation.

In the [2020 paper _"Proof-Carrying Data from Accumulation
Schemes"_](https://eprint.iacr.org/2020/499.pdf), that this project heavily
relies on, the authors presented a generalized version of the previous
accumulation structure of Halo that they coined _Accumulation Schemes_.
Simply put, given a predicate $\Phi: \Instance^m \to \{ \top, \bot \}$,
where $m$ represents the number of $q$s accumulated for each proof step and
may vary for each time $\ASProver$ is called. An accumulation scheme then
consists of the following functions:

- $\ASProver(\vec{q}_i: \Instance^m, acc_{i-1}: \Acc) \to \Acc$

    The prover accumulates the instances $\{ q_1, \dots, q_m \}$ in $\vec{q}_i$ into the
    previous accumulator $acc_{i-1}$ into the new accumulator $acc_i$.

- $\ASVerifier(\vec{q}_i: \Instance^m, acc_{i-1}: \Option(\Acc), acc_i: \Acc) \to \Result(\top, \bot)$

    The verifier checks that the instances $\{ q_1, \dots, q_m \}$ in $\vec{q}_i$ was
    correctly accumulated into the previous accumulator $acc_{i-1}$ to form
    the new accumulator $acc_i$. The second argument $acc_{i-1}$ is modelled
    as an $\Option$ since for the first accumulation being done, there will
    be no accumulator. In all other cases, the second argument $acc_{i-1}$
    must be set to the previous accumulator.

- $\ASDecider(acc_i: \Acc) \to \Result(\top, \bot)$

    The decider performs a single check that simultaneously ensures that
    _every_ previous instance-proof pair accumulated in $acc_{i+1}$ verifies,
    assuming the $\ASVerifier$ has accepted that every previous accumulator
    correctly accumulates each $\{ q_1, \dots, q_m \}$ in each $\vec{q}_i$.

We define completeness and soundness informally for the Accumulation Scheme:

- **Completeness:** For all accumulators $acc_i$ and predicate inputs
  $\vec{q}_i \in \Instance^m$, if $\top = \ASDecider(acc) = \Phi(\vec{q}_i)$,
  then for $\ASProver(\vec{q}_i, acc_{i-1}) = acc_i$ it holds that $\top =
  \ASVerifier(acc_{i-1}, \vec{q}_i, acc_i) = \ASDecider(acc_i)$.

- **Soundness:** For all efficiently-generated accumulators $acc_{i-1}, acc_i
  \in \Acc$ and predicate inputs $\vec{q}_i \in \Instance^m$, if $\top = \ASDecider(acc_{i+1}) =
  \ASVerifier(\vec{q}_i, acc_{i-1}, acc_{i+1})$ then, with all but negligible probability,
  $\top = \Phi(\vec{q}_i) = \ASDecider(acc_i)$.

### IVC from Accumulation Schemes

In order to construct and IVC-scheme, we first present a SNARK with
parital succinct verification, that proves a single run of $F$ and can be
used with accumulation. This SNARK can be constructed using general-purpose
zero-knowledge proof scheme based on a PCS as described in the PCS section. To
help the reader we define $\Proof = (\Instance^m, \Option(\Acc), \Acc)$. Also,
as is the case for the accumulation scheme, the accumulator inputs are
represented with $\Option(\Acc)$ to highlight the base case of $s_0$. Below
is the definition of the SNARK:

- $\SNARKProver(a: A, R: A \to B, acc_{i-1}: \Option(\Acc)) \to (b, \Proof)$:  
  Outputs $\pi_i = (\vec{q}, acc_{i-1}, acc_i)$ that proves the statement
  that $b = R(a) \in B$, where:
  - $\vec{q} \in \Instance^m$: Represents the polynomial commitment openings.
  - $acc_i \in \Acc$: Represents the accumulation scheme accumulator. The $\SNARKProver$
    will run $\ASProver(\vec{q}, acc_{i-1}) = acc_i$ to accumulate the
    instances $\vec{q}$ into the new accumulator $acc_i$, allowing succinct
    verification.
- $\SNARKVerifierFast(R: A \to B, b: B, \pi_i = (\vec{q}, acc_{i-1}, acc_i): \Proof) \to \Result(\top, \bot)$:  
  Partially checks a proof $\pi_i$, in sub-linear time, i.e:
    $$\top \meq \ASVerifier(\vec{q}, acc_{i-1}, acc_i) \land I_R(\vec{q})$$
  Where $I_R \in \Instance^m \times B \to \{ \top, \bot \}$ represents a
  sub-linear[^IR] function that checks identities between evaluations, $v_j =
  p_j(z_j)$, in $(C_j, d, z_j, v_j, \pi^{(j)}_{Eval}) = q_j \in \vec{q}$,
  the circuit $R$ and the claimed output $b$, that must hold in order for
  $b = R(a)$ to be true. So for $\pi_i$ to be a valid proof, all $q_j \in
  \vec{q}$ must check and the identities represented by $I_R$ must hold:
  $\forall q_j \in \vec{q} : \PCCheck(q_j) \land I_R(\vec{q}, b) = \top$.
- $\SNARKVerifierSlow(R: A \to B, b: B, \pi_i = (\_, \_, acc_i) : \Proof) \to \Result(\top, \bot)$:  
  Fully checks a proof $\pi_i$, in possibly linear time, i.e:
    $$\top \meq \SNARKVerifierFast(R, b, \pi_i) \meq \ASDecider(acc_i)$$

It's easy to see why the above works, the checks normally made by
the general-purpose zero-knowledge proof scheme will all be performed
succinctly by $\ASVerifier$. This does not yet yield soundness, but since the
$\SNARKVerifierSlow$ also check the accumulator for the instances $acc_i$
using $\ASDecider$, by the security properties of $\AS$ and the general
purpose zero-knowledge proof scheme used, the SNARK construction above will
inherit the same level of security. We'll loosely look at the properties of
soundness and completeness:

For completeness, we first look at the check made by the $\SNARKVerifierFast$:
  $$\top \meq \SNARKVerifierFast(R, b, \pi_i) \meq \ASDecider(acc_i)$$
  $$\top \meq \ASVerifier(\vec{q}, acc_{i-1}, acc_i) \meq I_R(\vec{q}, b) \meq \ASDecider(acc_i)$$
Firstly, see that since the prover runs $\ASProver$ honestly, by the
completeness of $\AS$, $\ASVerifier(\vec{q}, acc_{i-1}, acc_i) = \top
\land \ASDecider(acc_i) = \top$. The above construction must be based on
a general purpose zero-knowledge scheme, and assuming that it's complete,
$I_{R_F}(\vec{q}, b) = \top$. Putting these together the check done in
$\SNARKVerifierSlow$ will always pass, and as such, we have completeness. The
soundness will depend on the underlying general purpose zero-knowledge proof
scheme and $\AS$. $\SNARKVerifierFast$ will trivially have completeness,
but obviously no soundness, which may not be useful on its own, but we
will use it in the IVC scheme. Also note that a single step of IVC can be
performed using the above construction $\SNARKProver(s_0, R_F, \bot) = \pi$
then, $\SNARKVerifierSlow(R_F, \pi) = \top$.

At the surface, the SNARK construction may not seem particularly useful, as
the added complexity does not even allow for proof recursion. All we get is
unneccesarily larger proof sizes. The above specification may also seem overly
abstract, why not hardcode $R = R_F$ representing the transition function
$F$? Well, the abstractness arises since the above SNARK construction is
also used to prove the IVC claim $R_{IVC}$, allowing us to simply reuse the
above SNARK definition.  With the above SNARK construction we can acheive
IVC with Accumulation Schemes:

- $\IVCProver(s_{i-1}: S, R_F: S \to S, \pi_F^{(i)} = (\_, \_, acc_{i-1}): \Option(\Proof)) \to (S, (\Proof, \Proof))$

  1. Runs $\SNARKProver(s_{i-1}, R_F, acc_{i-1}) = \pi_F^{(i)} = (\vec{q}_i, I_F, acc_i)$.
  2. Then generate a SNARK proof $\pi_{IVC}^{(i)}$ using the following claim,
     expressed as a circuit $R_{IVC} \in \Proof \to \{ \top, \bot \}$,
     with $s_0$ being public:
       $$R_{IVC} := \text{I.K} \; \pi_F^{(i)} = (\vec{q}_i, \_, \_) \; \text{s.t.} \; I_F(\vec{q}_i, s_i) \meq \top \land (s_{i-1} \meq s_0 \lor \SNARKVerifierFast(R_F, s_i, \pi_F^{(i)}) \meq \top)$$
  3. Run $\SNARKProver(s_{i-1}, R_{IVC}, acc_i) = \pi_{IVC}^{(i)}$.
  4. Output $\pi_i = (s_i, (\pi_{IVC}^{(i)}, \pi_F^{(i)}))$

- $\IVCVerifier(R_{IVC}: \Proof \to \{ \top, \bot \}, s_i: S, \pi_{IVC}^{(i)}: \textbf{Proof}) \to \Result(\top, \bot)$

  1. Checks the proof: $\SNARKVerifierSlow(R_{IVC}, s_i, \pi_{IVC}^{(i)}) \meq \top$

A visualization of the chain of proofs can be seen below:

\begin{figure}[!H]
\centering
\begin{tikzpicture}[node distance=2cm]

  % Nodes
  \node (s0) [node] {$s_0$};
  \node (s1) [node, right=of s0] {$(s_1, \pi_1)$};
  \node (dots) [right=2cm of s1] {$\dots$};
  \node (sn) [node, right=3cm of dots] {$(s_n, \pi_n)$};

  % Arrows with labels
  \draw[arrow] (s0) -- node[above] {$\Pc(s_0, \bot)$} (s1);
  \draw[arrow] (s1) -- node[above] {$\Pc(s_1, \pi_1)$} (s2);
  \draw[arrow] (dots) -- node[above] {$\Pc(s_{n-1}, \pi_{n-1})$} (sn);

\end{tikzpicture}
\caption{
  A visualization of the relationship between $F, \vec{s}$ and $\vec{\pi}$
  in an IVC setting using Accumulation Schemes. Where each $\pi_i$ is a pair
  representing a proof used to verify the IVC relation, $\pi_{IVC}^{(i)}$
  and a proof used to prove new recursive proofs, $\pi_F^{(i)}$, so $\pi_i =
  (\pi_{IVC}^{(i)}, \pi_F^{(i)})$. $\Pc$ is defined to be $\Pc(s_{i-1},
  \pi_{i-1}) = \IVCProver(s_{i-1}, R_F, \pi_F^{(i-1)}) = (s_i, \pi_i)$.
}
\end{figure}

Consider the above chain run $n$ times. As in the "simple" SNARK IVC
construction, if the SNARK verifier accepts at the end, then we get a chain
of implications:

$$
\begin{alignedat}[b]{2}
  &\SNARKVerifierSlow(R_{IVC}, s_n, \pi_{IVC}^{(n)}) = \top                                              &&\then \\
  &I_F(\vec{q}_{n-1}, s_{n-1}) \land \ASVerifier(\vec{q}_{n-1}, acc_{n-1}, acc_n) = \top            &&\then \\
  &I_F(\vec{q}_{n-2}, s_{n-2}) \land \ASVerifier(\vec{q}_{n-2}, acc_{n-2}, acc_{n-1}) = \top        &&\then \dots \\
  &I_F(\vec{q}_1, s_1)         \land \ASVerifier(\vec{q}_1, \bot, acc_1) = \top                     &&\then \\
\end{alignedat}
$$

And since the above $\SNARKVerifierSlow$ performs the $\ASDecider$ check, on
the accumulator that contains all $\vec{q}_i$ used for the $\vec{\pi_F^{(i)}}$
proofs, the opening proofs used for $I_F$ will be valid, which gives us:

$$
\begin{alignedat}[b]{2}
  &\SNARKVerifierSlow(\pi_{IVC}^{(i)}) = \top  &&\then \\
  &s_n = F(s_{n-1})                            &&\then \\
  &s_{n-1} = F(s_{n-2})                        &&\then \dots \\
  &s_1 = F(s_0)                                &&\then \\
\end{alignedat}
$$

Completeness should follow rather trivially using the above argument, but
we will again loosely argue soundness. We want to show that $s_n = F^n(s_0)$
which is equivalent to:

$$
\begin{alignedat}[b]{8}
  &s_n = F(s_{n-1})                            &&\quad \land \; && \\
  &s_{n-1} = F(s_{n-2})                        &&\quad \land \; && \dots \\
  &s_1 = F(s_0)                                &&\quad \land \; && \\
\end{alignedat}
$$

By the soundness property of the Accumulation Scheme, an instance $\vec{q}_i
\in \Instance^m$ will be valid if $\top = \ASVerifier(\vec{q}_i, acc_{i-1},
acc_i) = \ASDecider(acc_i)$, so if all the accumulators $\vec{acc} \in \Acc^n$
are valid, then all the instances will be valid. This is exactly the case
due to the definition of the decider whereby checking an accumulator $acc_n$
ensures that every previous instance is valid, provided that all previous
$\ASVerifier$s accepted. Finally, if the underlying general-purpose
zero-knowledge proof scheme is sound, then, provided that all PCS openings
$\vec{q}$ are valid, each $I_F(s_i, \pi_F^{(i)})$ will be true. So the
soundness of the above protocol should depend on the underlying protocols used[^unsoundness].

<!-- TODO: This entire section -->
\begin{quote}
\color{GbGrey}

\textbf{Sidenote: an example using Plonk and $\PCDL$:}

If we take Plonk as a concrete example, then the verifier receives
a series of evaluation proofs along with their commitments $\PCDLCommit(C_i, d,
z_i, v_i, \pi_i)$, evaluation points $v = p(z)$, and since the verifier chose
the polynomial inputs $z$, the verifier can construct a list of instances:

  $$(q_1 = (C_1, d, z_1, v_1, \pi_1), \dots, q_m = (C_m, d, z_m, v_m, \pi_m))$$

The verifier will then check all these openings, using the succinct checks
that must run in sublinear time:

  $$\PCDLSuccinctCheck(C_1, d, z_1, v_1, \pi_1) \meq \dots \meq \PCDLSuccinctCheck(C_m, d, z_m, v_m, \pi_m) \meq \top$$

And additionally check relations between $\vec{v} \in \Fb^m$ satisfy
the public circuit $R_F$ using $I_{R_F}$. This will check the validity of
the computation of a single $s_i$ $(s_i \meq R_F(s_{i-1}))$.

To modify the plonk protocol slightly, we can make the Plonk Prover

These claims $\vec{q}_i \in \Fb^m$ will then be accumulated into the new
accumulator, $acc_i$, along with the old accumulator, $acc_{i-1}$. Due to
the soundness properties of $\PCDL$ and the accumulation scheme, performing
the succinct checks will be sufficient, provided that you run $\ASDecider$
at the end of the IVC scheme.

\end{quote}

[^IR]: If $I_R$ is not sub-linear in the underlying general-purpose
zero-knowledge proof scheme, then the above construction will not work for IVC.
[^unsoundness]: A more thorough soundness discussion would reveal that running
the extractor on a proof-chain of length $n$ would mean that we don't get the
desired soundness, as argued by Valiant in his original 2008 paper. Instead
he constructs a proof tree of size $\Oc(\lg(n))$ size, which gets around the
issue. In practice however, this is not assumed to be a real security issue,
and practical applications conjecture that the failure of the extractor does
not lead to any real-world attack, thus still acheiving constant proof sizes.

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
proofs of zero-knowledge.

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

  Creates a commitment to the coefficients of the polynomial $p$ of degree
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
  \Desc{$\EvalProof$}{
    Proof that states: "I know $p \in \Fb^d_q[X]$ with commitment $C \in
    \Eb(\Fb_q)$ s.t. $p(z) = v$"
  }
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
$p$ s.t. $p(z) = v = \dotp{\vec{c_0}}{\vec{z_0}}$. So because $z$ is public, we
can get away with omitting the generators, $(\vec{H})$, for $\vec{b}$ which
we would otherwise need in the Bulletproofs IPA. For efficiency we also
send along the curve point $U = G^{(0)}$, which the original IPA does not
do. The $\PCDLSuccinctCheck$ uses $U$ to make its check and $\PCDLCheck$
verifies the correctness of $U$.

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

The $\PCDLSuccinctCheck$ algorithm performs the same check as in the
Bulletproofs protocol. With the only difference being that instead of calculating
$G^{(0)}$ itself, it trusts that the verifier sent the correct $U = G^{(0)}$ in
the prover protocol, and defers the verification of this claim to $\PCDLCheck$.

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

Since $\PCDLSuccinctCheck$ handles the verification of the IPA given that
$U = G^{(0)}$, we run $\PCDLSuccinctCheck$, then check that $U \meq G^{(0)}
= \CMCommit(\vec{G}, \vec{h}, \bot) = \ip{\vec{G}}{\vec{h}}$.

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
same inputs and, given that $\ASDLProver$ is honest, will therefore get the
same outputs, these outputs are checked to be equal to the ones received from
the prover. Since these were generated honestly by the prover, also using
$\ASDLCommonSubroutine$, the $\ASDLVerifier$ will accept with probability 1,
returning $\top$. Intuitively, this also makes sense. It's the job of the
verifier to verify that each instance is accumulated correctly into the
accumulator. This verifier does the same work as the prover and checks that
the output matches. Also note that the common subroutine calls
$\PCDLSuccinctCheck$ on each instance, thus the only remaining work is to
run the full check on each instance.

As for the $\ASDLDecider$, it just runs $\PCDLCheck$ on the provided
accumulator, which represents a evaluation proof i.e. an instance. This
check will always pass, as the prover constructed it honestly.

\begin{quote}
\color{GbGrey}

\textbf{Why does checking $acc_i$ check all previous instances $\vec{q}$
and previous accumulators $\vec{acc}$?}

The $\ASDLProver$ runs the $\ASDLCommonSubroutine$ that creates an accumulated
polynomial $h$ from $\vec{h}$ that is in turn created for each instance $q_j
\in \vec{q}_i$ by $\PCDLSuccinctCheck$:

$$h_i(X) := \prod^{lg(n)}_{i=0} (1 + \xi_{\lg(n)-i} \cdot X^{2^i}) \in F_q[X]$$

We don't mention the previous accumulator $acc_{i-1}$ explicitly as it's
treated as an instance in the protocol. The $\ASDLVerifier$ shows that $C$
is a commitment to $h$ in the sense that it's a linear combination of all
$h$'s from the previous instances, by running the same $\ASDLCommonSubroutine$
algorithm as the prover to get the same output. Note that the $\ASDLVerifier$
does not guarantee that $C$ is a valid commitment to $h(X)$ in the sense that
$C = \PCDLCommit(h, \bot)$, that's the verifiers job. Since $\ASDLVerifier$
does not show that each $U_i$ is valid, and therefore that $C = \PCDLCommit(h,
\bot)$, we now wish to show that the second pass checks for all instances
that has been accumulated into the accumulator $acc_i$.

\textbf{Showing that $C = \PCDLCommit(h, \bot)$:}

The $\ASDLProver$ has a list of instances $\vec{q}_i$, then runs
$\PCDLSuccinctCheck$ on each $q_j \in \vec{q}_i$ of them, getting $(U_1,
\dots, U_m)$ and $(h_1(X), \dots, h_m(X))$. For each element $U_i$ in the
vector $\vec{U} \in \Eb(\Fb_q)^m$ and each element $h_i(X)$ in the vector
$\vec{h} \in (\Fb^{\leq d}_q[X])^m$, the $\ASDLProver$ defines:

$$h(X) := \sum^{m}_{i=0} \a^i \cdot h_i(X)$$
$$C := \sum^{m}_{i=0} \a^i \cdot U_i$$

Since we know from the $\ASDLVerifier$

\begin{enumerate}
  \item $h(X)$ and $C$ is constructed as above.
  \item
     The $\ASDLVerifier$ also runs $\PCDLSuccinctCheck$, therefore we know
     that for each instance $q_i$ (and the previous accumulator $acc_{i-1}$)
     $\Phi(q_i) = \top$, provided that the second check passes $U_i \meq
     \PCDLCommit(h_i, \bot)$.
\end{enumerate}

\textgrey{We first show that if $C$ is a valid commitment to $h(X)$, then that implies
that each $U_i$ is a valid commitment to $h_i$, $U_i = \PCDLCommit(h_i(X),
\bot) = \ip{\vec{G}}{\vec{h_i}}$, thereby performing the second check of
$\PCDLCheck$, on all $q_j$ instances at once. When the $\ASDLDecider$ runs
$\PCDLCheck$, thereby performing the second check $C \meq \PCDLCommit(h(X),
\bot)$ on h(X), they effectively check that $C$ is a valid commitment to $h$. If
this is not the case, then for at least one of the $U_i$'s $U_i \neq
\PCDLCommit(h_i, \bot)$. That means that running the $\ASDLDecider$ corresponds
to checking all $U_i$'s.}

\textgrey{What about checking the previous instances, $\vec{q}_{i-1}$, accumulated into
the previous accumulator, $acc_{i-1}$? The accumulator for $\vec{q}_{i-1}$
is represented by an instance $acc_{i-1} = (C = \PCDLCommit(h_{acc_{i-1}},
\bot), d, z, v = h_{acc_{i-1}}(z), \pi)$, which, as mentioned, behaves
like all other instances in the protocol and represents a PCS opening
to $h_{acc_{i-1}}(X)$. Since $acc_{i-1}$ is represented as an instance,
and we showed that as long as each instance is checked by $\ASVerifier$
(which $acc$ also is), running $\PCDLCheck(acc_i)$ on the corresponding
accumulation polynomial $h_{acc_i}(X)$ is equivalent to performing the second
check $U_i = \PCDLCommit(h_i(X), \bot)$ on all the $h_i$ that $h_{acc_i}(X)$
consists of. Therefore, we will also check the previous set of instances
$\vec{q}_{i-1}$, and by induction, all accumulated instances $\vec{q}$
and accumulators $\vec{acc}$.}



\end{quote}



<!-- TODO: Maybe explain why $C, d, z, v, \o$ are valid -->

## Soundness

# Benchmarks

Each benchmark is run using two helper functions, one for generating the
benchmark data, and one used for checking the accumulators.

```rust {.numberLines}
  pub fn acc_cmp_s_512_10(c: &mut Criterion) {
      let (_, _, accs) = acc_compare(512, 10);
      c.bench_function("acc_cmp_s_512_10", |b| {
          b.iter(|| acc_compare_slow_helper(accs.clone()).unwrap())
      });
  }

  pub fn acc_cmp_f_512_10(c: &mut Criterion) {
      let (d, qss, accs) = acc_compare(512, 10);
      c.bench_function("acc_cmp_f_512_10", |b| {
          b.iter(|| acc_compare_fast_helper(d, &qss, accs.clone()).unwrap())
      });
  }
```

In the code below, `acc_compare`, is the function that creates the data
required to run the tests. The function `acc_compare_fast_helper` runs
$\ASVerifier$ on all instances and accumulators, and finally runs the decider
once on the final accumulator, meaning that all instances are verified. The
other helper function `acc_compare_slow_helper` naively runs the decider on
all instances, which also checks all instances, but is a lot slower, as can
also be seen in the benchmarks.

```rust {.numberLines}
  fn acc_compare(n: usize, k: usize) -> (usize, Vec<Vec<Instance>>, Vec<Accumulator>) {
      let mut rng = test_rng();
      let d = n - 1;
      let mut accs = Vec::with_capacity(k);
      let mut qss = Vec::with_capacity(k);

      let mut acc: Option<Accumulator> = None;

      for _ in 0..k {
          let q = random_instance(&mut rng, d);
          let qs = if let Some(acc) = acc {
              vec![acc.into(), q]
          } else {
              vec![q]
          };

          acc = Some(acc::prover(&mut rng, d, &qs).unwrap());

          accs.push(acc.as_ref().unwrap().clone());
          qss.push(qs);
      }
      (d, qss, accs)
  }

  fn acc_compare_fast_helper(
    d: usize,
    qss: &[Vec<Instance>],
    accs: Vec<Accumulator>
  ) -> Result<()> {
      let last_acc = accs.last().unwrap().clone();

      for (acc, qs) in accs.into_iter().zip(qss) {
          acc::verifier(d, qs, acc)?;
      }

      acc::decider(last_acc)?;

      Ok(())
  }

  fn acc_compare_slow_helper(accs: Vec<Accumulator>) -> Result<()> {
      for acc in accs.into_iter() {
          acc::decider(acc)?;
      }

      Ok(())
  }
```

The results of the benchmarks, can be seen below:

**Benchmarking (10 iterations)**
\begin{tikzpicture}
\begin{axis}[
    title={Benchmark Times for 10 Iterations},
    xlabel={The maximum degree bound $d$, plus 1},
    ylabel={Time (ms)},
    xtick=data,
    legend pos=north west,
    ymajorgrids=true,
    grid style=dashed,
    symbolic x coords={512, 1024, 2048, 4096, 8196, 16384},
    enlarge x limits=0.2
]
\addplot coordinates {(512, 94.834) (1024, 151.25) (2048, 258.92) (4096, 453.55) (8196, 838.05) (16384, 1522.7)};
\addplot coordinates {(512, 67.098) (1024, 77.597) (2048, 99.973) (4096, 139.35) (8196, 186.34) (16384, 299.49)};
\legend{acc\_cmp\_s, acc\_cmp\_f}
\end{axis}
\end{tikzpicture}

**Benchmarking (100 iterations)**
\begin{tikzpicture}
\begin{axis}[
    title={Benchmark Times for 100 Iterations},
    xlabel={The maximum degree bound $d$, plus 1},
    ylabel={Time (ms)},
    xtick=data,
    legend pos=north west,
    ymajorgrids=true,
    grid style=dashed,
    symbolic x coords={512, 1024, 2048, 4096, 8196, 16384},
    enlarge x limits=0.2
]
\addplot coordinates {(512, 940.91) (1024, 1504.2) (2048, 2557.9) (4096, 4494.5) (8196, 8372.3) (16384, 15253)};
\addplot coordinates {(512, 607.28) (1024, 662.03) (2048, 798.48) (4096, 1014.2) (8196, 1161.1) (16384, 1648.4)};
\legend{acc\_cmp\_s, acc\_cmp\_f}
\end{axis}
\end{tikzpicture}

**Benchmarking (1000 iterations)**
\begin{tikzpicture}
\begin{axis}[
    title={Benchmark Times for 1000 Iterations},
    xlabel={The maximum degree bound $d$, plus 1},
    ylabel={Time (s)},
    xtick=data,
    legend pos=north west,
    ymajorgrids=true,
    grid style=dashed,
    symbolic x coords={512, 1024, 2048, 4096, 8196, 16384},
    enlarge x limits=0.2
]
\addplot coordinates {(512, 9.4381) (1024, 15.087) (2048, 25.621) (4096, 44.970) (8196, 82.643) (16384, 152.63)};
\addplot coordinates {(512, 6.0183) (1024, 6.5114) (2048, 7.7752) (4096, 9.7851) (8196, 10.899) (16384, 15.176)};
\legend{acc\_cmp\_s, acc\_cmp\_f}
\end{axis}
\end{tikzpicture}

Unsurprisingly, increasing the number of iterations only changes the
performance difference up to a certain point, as the difference between
running the decider once and many times gets amortized away as the number
of iterations approaches infinity. Also, as was hoped for in the beginning
of the project, the performance of the two approaches show the expected
theoretical runtimes. The relatively low number degree bounds tested is due
to the fact that the $\vec{G}$'s are represented as constants in the code,
and that increasing the length of $\vec{G}$ significantly above 16384 leads
to slow compilation and failing LSP's. The solution is to handle $\vec{G}$
differently, but this was not done due to time constraints.

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
| I.K $w$                                                                         | "I Know", Used in the context of proof claims, meaning I have knowledge of the witness $w$                |
| $\Option(T)$                                                                    | $\{ T, \bot \}$                                                                                           |
| $\Result(T, E)$                                                                 | $\{ T, E \}$                                                                                              |
| $\EvalProof$                                                                    | $(\Eb^{lg(n)}(\Fb_q), \Eb^{lg(n)}(\Fb_q), \Eb(\Fb_q), \Fb_q\mathblue{, \Eb(\Fb_q), \Fb_q})$               |
| $\AccHiding$                                                                    | $(\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q)$                                                                       |
| $\Acc$                                                                          | $((\Eb(\Fb_q), \Nb, \Fb_q, \Fb_q, \EvalProof), \AccHiding)$                                               |

Note that the following are isomorphic $\{ \top, \bot \} \iso \Option(\top) \iso
\Result(\top, \bot)$, but they have different connotations. Generally for
this report, $\Option(T)$ models optional arguments, where $\bot$ indicates
an empty argument and $\Result(T, \bot)$ models the result of a computation
that may fail, particularly used for rejecting verifiers.

## Raw Benchmarking Data

The raw benchmarking data provided by Criterion.

```None
  acc_cmp_s_512_10        time:   [94.245 ms 94.834 ms 95.584 ms]
  acc_cmp_s_1024_10       time:   [150.47 ms 151.25 ms 152.39 ms]
  acc_cmp_s_2048_10       time:   [257.25 ms 258.92 ms 261.14 ms]
  acc_cmp_s_4096_10       time:   [451.60 ms 453.55 ms 456.18 ms]
  acc_cmp_s_8196_10       time:   [833.82 ms 838.05 ms 843.10 ms]
  acc_cmp_s_16384_10      time:   [1.5172 s 1.5227 s 1.5292 s]
  acc_cmp_f_512_10        time:   [66.989 ms 67.098 ms 67.220 ms]
  acc_cmp_f_1024_10       time:   [77.033 ms 77.597 ms 78.330 ms]
  acc_cmp_f_2048_10       time:   [99.415 ms 99.973 ms 100.68 ms]
  acc_cmp_f_4096_10       time:   [138.50 ms 139.35 ms 140.44 ms]
  acc_cmp_f_8196_10       time:   [185.41 ms 186.34 ms 187.59 ms]
  acc_cmp_f_16384_10      time:   [297.72 ms 299.49 ms 301.88 ms]
  acc_cmp_s_512_100       time:   [937.12 ms 940.91 ms 945.67 ms]
  acc_cmp_s_1024_100      time:   [1.4986 s 1.5042 s 1.5107 s]
  acc_cmp_s_2048_100      time:   [2.5490 s 2.5579 s 2.5681 s]
  acc_cmp_s_4096_100      time:   [4.4822 s 4.4945 s 4.5077 s]
  acc_cmp_s_8196_100      time:   [8.2672 s 8.3723 s 8.5111 s]
  acc_cmp_s_16384_100     time:   [15.240 s 15.253 s 15.271 s]
  acc_cmp_f_512_100       time:   [604.98 ms 607.28 ms 610.61 ms]
  acc_cmp_f_1024_100      time:   [658.74 ms 662.03 ms 666.03 ms]
  acc_cmp_f_2048_100      time:   [795.23 ms 798.48 ms 802.54 ms]
  acc_cmp_f_4096_100      time:   [1.0099 s 1.0142 s 1.0194 s]
  acc_cmp_f_8196_100      time:   [1.1559 s 1.1611 s 1.1671 s]
  acc_cmp_f_16384_100     time:   [1.6414 s 1.6484 s 1.6564 s]
  acc_cmp_s_512_1000      time:   [9.4209 s 9.4381 s 9.4555 s]
  acc_cmp_s_1024_1000     time:   [15.059 s 15.087 s 15.135 s]
  acc_cmp_s_2048_1000     time:   [25.604 s 25.621 s 25.638 s]
  acc_cmp_s_4096_1000     time:   [44.951 s 44.970 s 44.990 s]
  acc_cmp_s_8196_1000     time:   [82.605 s 82.643 s 82.697 s]
  acc_cmp_s_16384_1000    time:   [152.43 s 152.63 s 152.93 s]
  acc_cmp_f_512_1000      time:   [6.0046 s 6.0183 s 6.0325 s]
  acc_cmp_f_1024_1000     time:   [6.4971 s 6.5114 s 6.5262 s]
  acc_cmp_f_2048_1000     time:   [7.7599 s 7.7752 s 7.7906 s]
  acc_cmp_f_4096_1000     time:   [9.7686 s 9.7851 s 9.8022 s]
  acc_cmp_f_8196_1000     time:   [10.887 s 10.899 s 10.910 s]
  acc_cmp_f_16384_1000    time:   [15.166 s 15.176 s 15.186 s]
```

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
