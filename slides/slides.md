---
title: Investigating IVC with Accumulation Schemes
author:
  - Rasmus Kirk Jakobsen
theme: Berlin
institute: Computer Science Aarhus
fontsize: 9pt
lang: en-US
section-titles: true
toc: true
---

# Overview

## Introduction
- TODO:
- TODO:
- TODO:

# Simple IVC

## Motivation

\begin{block}{IVC is designed to solve the following problem:}
  \vspace{0.6em}
  \begin{quote}
    \color{Gray}
    If a computation runs for hundreds of years and ultimately outputs 42,
    how can we check its correctness without re-executing the entire process?
  \end{quote}
  \vspace{0.4em}
\end{block}

\begin{block}{We define the transition function $F$ run on an initial state $s_0$:}
\vspace{0.5em}
\centering
\begin{tikzpicture}[node distance=2cm]

  % Nodes
  \node (s0) [node] {$s_0$};
  \node (s1) [node, right=of s0] {$s_1$};
  \node (dots) [right=2cm of s1] {$\dots$};
  \node (sn) [node, right=2cm of dots] {$s_n$};

  % Arrows with labels
  \draw[thick-arrow] (s0) -- node[above] {$F(s_0)$} (s1);
  \draw[thick-arrow] (s1) -- node[above] {$F(s_1)$} (dots);
  \draw[thick-arrow] (dots) -- node[above] {$F(s_{n-1})$} (sn);

\end{tikzpicture}
\vspace{0.5em}
\end{block}

- _How can we verify $F^n(s_0)$ without re-executing the computation?_

## IVC chain

\begin{block}{We can use a SNARK to prove each computation step:}
  \vspace{0.5em}
  \centering
  \begin{tikzpicture}[node distance=1.75cm]
    % Nodes
    \node (s0) [node] {$s_0$};
    \node (s1) [node, right=of s0] {$(s_1, \pi_1)$};
    \node (dots) [right=1.75cm of s1] {$\dots$};
    \node (sn) [node, right=2.25cm of dots] {$(s_n, \pi_n)$};
    % Arrows with labels
    \draw[thick-arrow] (s0) -- node[above] {$\Pc(s_0, \bot)$} (s1);
    \draw[thick-arrow] (s1) -- node[above] {$\Pc(s_1, \pi_1)$} (dots);
    \draw[thick-arrow] (dots) -- node[above] {$\Pc(s_{n-1}, \pi_{n-1})$} (sn);
  \end{tikzpicture}
  \vspace{0.5em}
\end{block}

### $\Pc(s_i, \pi_i)$ represents:
  - $R := \text{I.K.} \; w = \{ \pi_{i-1}, s_{i-1} \} \; \text{ s.t. }$
    - $s_i \meq F(s_{i-1}) \; \land \; (s_{i-1} \meq s_0 \lor \Vc(R_F, x = \{ s_0, s_i \}, \pi_{i-1}))$
  - $\pi_i = \SNARKProver(R_F, x = \{ s_0, s_i \}, w = \{ s_{i-1}, \pi_{i-1} \})$
  - $s_i = F(s_{i-1})$

## Proof

- $R$ gives us a series of proofs of the claims:
$$
\begin{alignedat}{7}
  &\text{I.K.} \; \pi_{n-1} \; &&\text{ s.t. } \; &&s_n     &&= F(s_{n-1}) \; &&\land \; (s_{n-1} = s_0  &&\lor \Vc(R, x, \pi_{n-1}) = \top), \\
  &\text{I.K.} \; \pi_{n-2} \; &&\text{ s.t. } \; &&s_{n-1} &&= F(s_{n-2}) \; &&\land \; (s_{n-2} = s_0  &&\lor \Vc(R, x, \pi_{n-2}) = \top), \; \dots \\
  &                            &&              \; &&s_1     &&= F(s_0)     \; &&\land \; (s_0 = s_0      &&\lor \Vc(R, x, \pi_0) = \top)
\end{alignedat}
$$
- Which, if all verify means that:
$$
\begin{alignedat}{4}
  &\SNARKVerifier(R, x, \pi_n) = \top \implies \\
  &s_n = F(s_{n-1}) \; \land \; \\
  &\SNARKVerifier(R, x, \pi_{n-1}) = \top \implies \\
  &s_{n-1} = F(s_{n-2}) \; \land \\
  &\SNARKVerifier(R, x, \pi_{n-2}) = \top \implies \dots \\
  &s_1 = F(s_0)
\end{alignedat}
$$

# $\AS$ based on DL

## Overview

### Generally

- $\ASSetup(\l) \to \pp_\AS$
- $\ASProver(\vec{q}: \Instance^m, acc_{i-1}: \Acc) \to \Acc$
- $\ASVerifier(\vec{q}: \Instance^m, acc_{i-1}: \Option(\Acc), acc_i: \Acc) \to \Result(\top, \bot)$
- $\ASDecider(acc_i: \Acc) \to \Result(\top, \bot)$

### $\ASDL$: Based on Discrete Log

- $\ASDLSetup(1^\l, D) \to \pp_\AS$
- $\ASDLProver(\vec{q}: \Instance^m) \to \Result(\Acc, \bot)$:
- $\ASDLVerifier(\vec{q}: \Instance^m, \acc_i: \Acc) \to \Result(\top, \bot)$:
- $\ASDLDecider(\acc_i: \Acc) \to \Result(\top, \bot)$:
- $\ASDLCommonSubroutine(\vec{q}: \Instance^m) \to \Result((\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X]), \bot)$

## Prover

\begin{algorithm}[H]
\caption*{\textbf{Algorithm} $\ASDLProver$}
\textbf{Inputs} \\
  \Desc{$\vec{q}: \Instance^m$}{} \\
\textbf{Output} \\
  \Desc{$\Result(\Acc, \bot)$}{}
  \begin{algorithmic}[1]
  \Require $\forall d_i \in \vec{q}, \forall d_j \in \vec{q} : d_i = d_j \land d_i \leq D$
  \Require $(d_i+1) = 2^k$, where $k \in \Nb$
  \State Compute the tuple $(\bar{C}, d, z, h(X)) := \ASDLCommonSubroutine(\vec{q})$.
  \State Generate the evaluation proof $\pi := \PCDLOpen(h(X), \bar{C}, d, z \mathblue{, \o})$.
  \State Finally, output the accumulator $\acc_i = (\bar{C}, d, z, v := h(z), \pi)$.
\end{algorithmic}
\end{algorithm}

## Verifier

\begin{algorithm}[H]
\caption*{\textbf{Algorithm} $\ASDLVerifier$}
\textbf{Inputs} \\
  \Desc{$\vec{q}: \Instance^m$}{} \\
  \Desc{$\acc_i: \Acc$}{} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{}
  \begin{algorithmic}[1]
  \Require $(d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $\acc_i$ as $(\bar{C}, d, z, v, \_)$
    \State Compute $(\bar{C}', d', z', h(X)) := \ASDLCommonSubroutine(\vec{q})$
    \State Then check that $\bar{C}' \meq \bar{C}, d' \meq d, z' \meq z$, and $h(z) \meq v$.
\end{algorithmic}
\end{algorithm}

## Decider

\begin{algorithm}[H]
\caption{$\ASDLDecider$}
\textbf{Inputs} \\
  \Desc{$\acc_i: \Acc$}{} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{}
  \begin{algorithmic}[1]
  \Require $\acc_i.d \leq D$
  \Require $(\acc_i.d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $\acc_i$ as $(\bar{C}, d, z, v, \pi)$
    \State Check $\top \meq \PCDLCheck(\bar{C}, d, z, v, \pi)$
\end{algorithmic}
\end{algorithm}

## Common Subroutine

\begin{algorithm}[H]
\caption*{\textbf{Algorithm} $\ASDLCommonSubroutine$}
\textbf{Inputs} \\
  \Desc{$\vec{q}: \Instance^m$}{} \\
\textbf{Output} \\
  \Desc{$\Result((\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X]), \bot)$}{}
\begin{algorithmic}[1]
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Parse $d$ from $q_1$.
  \For{$j \in [0, m]$}
    \State Parse $q_j$ as a tuple $(C_j, d_j, z_j, v_j, \pi_j)$.
    \State Compute $(h_j(X), U_j) := \PCDLSuccinctCheck^{\rho_0}(C_j, d_j, z_j, v_j, \pi_j)$.
    \State Check that $d_j \meq d$
  \EndFor
  \State Compute the challenge $\a := \rho_1(\vec{h}, \vec{U})$
  \State Let the polynomial $h(X) := \sum^m_{j=1} \a^j h_j(X)$
  \State Compute: $\bar{C} := \sum^m_{j=1} \a^j U_j, \; z := \rho_1(C, h(X))$
  \State Output $(\bar{C}, D, z, h(X))$.
\end{algorithmic}
\end{algorithm}

## Why it works

- $\ASDLVerifier$ shows that $h(X), \bar{C}$ are linear combinations of $h_j(X), U_j$'s.
- $\ASDLDecider$ shows that $\bar{C} = \PCDLCommit(h(X), d, \bot)$, checks all $U_j$'s.
  - $\PCDLCheck$ shows that $C_{\acc_i}$ is a commitment to $h'(X)$ and $h'(z) = v_{\acc_i}$.
  - $\ASDLVerifier$ shows that $C_{\acc_i} = \sum_{j=1}^m \a^j U_j$, $h(z) = v_{\acc_i}$.
  - Since $v_{\acc_i} = h(z) = h'(z)$ then $h(X) = h'(X)$ with $\Pr[d/|\Fb_q|]$.
  - If $\exists j \in [m] : B_j \neq U_j$ then $U_j$ is not a valid commit to $h_j(X)$ and $C_{\acc_i} \neq \sum_{j=1}^m \a_j B_j$. I.e. $C_{\acc_i}$ is not a valid commit to $h_{\acc_i}(X)$. Unless,

  - Define $\forall j \in [m] : B_j = \ip{\vec{G}}{\vec{h_j}^{(\text{coeffs})}}$. If $\exists j
    \in [m]$ $B_j \neq U_j$ then:
    - $U_j$ is not a valid commitment to $h_j(X)$ and,
    - $\sum_{j=1}^m \a_j B_j \neq \sum_{j=1}^m \a_j U_j$

    As such $C_{\acc_i}$ will not be a valid commitment to $h_{\acc_i}(X)$. Unless,
  - $\a := \rho_1(\vec{h}, \vec{U})$ or $z = \rho_1(C, h(X))$ is constructed maliciously.
- Previous accumulators are instances, as such, they will also be checked.

# $\AS$ Completeness

- $\ASDLVerifier$:
  - Runs the same algorithm ($\ASDLCommonSubroutine$) with the same inputs
  - Given that $\ASDLProver$ is honest, $\ASDLVerifier$ will get the
    same outputs, these outputs are checked to be equal to the ones received
    from the prover.
  - Since these were generated honestly by the prover, also using
    $\ASDLCommonSubroutine$, the $\ASDLVerifier$ will accept with probability 1.

- $\ASDLDecider$:
  - Runs $\PCDLCheck$ on the provided accumulator, which represents a evaluation
    proof i.e. an instance. This check will always pass, as the prover
    constructed the accumulator honestly.

# $\AS$ Soundness

## Proving $\AS$ Soundness (1/6): The Zero Finding Game

- Let $\CM$ be a perfectly binding commitment scheme.
- Fix a maximum degree $D \in \Nb$ and a random oracle $\rho \in \CM \to F_\pp$.
- Then for every family of functions $\{f_\pp\}_\pp$ and fields $\{F_\pp\}_\pp$
  where:
  - $f_\pp \in \Mc \to F_\pp^{\leq D}[X]$
  - $F \in \Nb \to \Nb$
  - $|F_\pp| \geq F(\l)$ (usually $|F_\pp| \approx F(\l)$)

\vspace{0.5em}

- For every message format $L$ and computationally unbounded $t$-query oracle
  algorithm $\Ac$, the following holds:
$$
\Pr\left[
  \begin{array}{c}
    p \neq 0 \\
    \land \\
    p(z) = 0
  \end{array}
  \middle|
  \begin{array}{c}
    \rho \from \mathcal{U}(\l) \\
    \pp_\CM \gets \CMSetup(1^\l, L) \\
    (m, \omega) \gets \Ac^\rho(\pp_\CM) \\
    C \gets \CMCommit(m, \o) \\
    z \in F_{\pp} \from \rho(C) \\
    p := f_{\pp}(m)
  \end{array}
\right] \leq \sqrt{\frac{D(t+1)}{F(\l)}}
$$

## Proving $\AS$ Soundness (2/6): The Goal

$$
\Pr \left[
  \begin{array}{c|c}
    \begin{array}{c}
      \Vc^{\rho_1}((q_{\acc_{i-1}} \cat \vec{q}), \acc_i) = \top, \\
      \Dc^{\rho_1}(\acc_i) = \top \\
      \land \\
      \exists i \in [n] : \Phi_\AS(q_i) = \bot
    \end{array}
  & \quad
    \begin{array}{r}
      \rho_0 \leftarrow \Uc(\l), \rho_1 \leftarrow \Uc(\l), \\
      \pp_\AS \leftarrow \ASDLSetup^{\rho_1}_{1^\l}, \\
      (\vec{q}, \acc_{i-1}, \acc_i) \leftarrow \Ac^{\rho_1}_{\pp_\AS} \\
      q_{acc_{i-1}} \leftarrow \ToInstance(\acc_{i-1}) \\
    \end{array}
  \end{array}
\right]
$$

- $\Pr[\Ac] = \d$. We bound $\d$ by constructing, $\Bc_1, \Bc_2$, for the zero-finding game:
  - $\Pr[\Bc_1 \text{ wins} \land \Bc_2 \text{ wins}] = 0$
  - $\Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{ wins}] = \delta - \negl(\l)$
$$
\begin{aligned}
  \Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{ wins}] &= \Pr[\Bc_1 \text{ wins}] + \Pr[\Bc_2\text{ wins}] - \Pr[\Bc_1 \text{ wins} \land \Bc_2 \text{ wins}]\\
  \delta - \negl(\l)                              &\leq  \sqrt{\frac{D(t+1)}{F(\l)}} + \sqrt{\frac{D(t+1)}{F(\l)}} \\
  \delta                                          &\leq  2 \cdot \sqrt{\frac{D(t+1)}{|\Fb_q|}} + \negl(\l)         \\
\end{aligned}
$$

## Proving $\AS$ Soundness (3/6): The Commitment Schemes for $\Bc_1, \Bc_2$

- $\CM_a$:
  - $\CM_a.\Setup^{\rho_0}(1^\l, D) := \pp_\PC \from \PCDLSetup^{\rho_0}(1^\lambda, D)$
  - $\CM_a.\Commit((p(X), h(X)), \_) := (C \from \PCDLCommit(p(X), d, \bot), h)$
  - $\Mc_{\CM_1} := \{(p(X), h(X) = \a^j h_j(X))\} \in \Pc((\Fb_q^{\leq D}[X])^2)$
  - $z_a := \rho_1(\CM_1.\Commit((p(X), h(X)), \_)) = z_\acc$
- $\CM_a$:
  - $\CM_2.\Setup^{\rho_0}(1^\l, D) := \pp_\PC \from \PCDLSetup^{\rho_0}(1^\lambda, D)$
  - $\CM_2.\Commit([(h_j(X), U_j)]^m, \_) := [(h_j(X), U_j)]^m$:
  - $\Mc_b := \{[(h_j(X), U_j)]^m\} \in \Pc((\Fb_q^{\leq D}[X] \times \Eb(\Fb_q))^m)$
  - $z_b := \rho_1(\CM_2.\Commit([(h_j(X), U_j)]^m, \_)) = \rho_1([(h_j(X), U_j)]^m) = \a$

\vspace{1em}

- $f^{(a)}_\pp(p(X), h(X) = [h_j(X)]^m) := a(X) = p(X) - \sum_{j=1}^m \a^j h_j(X)$,
- $f^{(b)}_\pp(p = [(h_j(X), U_j)]^m) := b(X) = \sum_{j=1}^m b_j X^j$ where for each $j \in [m]$:
  - $B_j \leftarrow \PCDLCommit(h_j, d, \bot)$
  - Compute $b_j : b_j G = U_j - B_j$

## Proving $\AS$ Soundness (4/6): The intermediate adversary $\Cc$

\begin{algorithm}[H]
\caption*{\textbf{The Adversary} $\Cc^{\rho_1}(\pp_\PC)$}
\begin{algorithmic}[1]
  \State Parse $\pp_\PC$ to get the security parameter $1^\l$ and set $\AS$ public parameters $\pp_{\AS} := 1^\l$.
  \State Compute $(\vec{q}, \acc_{i-1}, \acc_i) \leftarrow \Ac^{\rho_1}(\pp_\AS)$.
  \State Parse $\pp_\PC$ to get the degree bound $D$.
  \State Output $(D, \acc_i = (C_\acc, d_\acc, z_\acc, v_\acc), \vec{q})$.
\end{algorithmic}
\end{algorithm}

- Running $\Ec_\Cc^{\rho_1}$ on $\Cc$ gives $p(X)$, given $\ASDLDecider$ accepts, with $\Pr[1 - \negl(\l)]$:
  - $C_\acc$ is a deterministic commitment to $p(X)$.
  - $p(z_\acc) = v_\acc$
  - $\deg(p) \leq d_\acc \leq D$

## Proving $\AS$ Soundness (5/6): Probabilities and Implications

\begin{block}{The $\ASDLDecider$, and $\ASDLVerifier$, will accept with probability $\d$, s.t}
  \vspace{-2em}
  $$E_\Dc := \exists j \in [m] : \Phi_\AS(q_j) = \bot \implies \PCDLCheck^{\rho_0}(C_j, d_j, z_j, v_j, \pi_j) = \bot$$
  $$
    \Pr[E_\Ec \land E_\Dc] = \Pr[E_\Ec \; | \; E_\Dc] \cdot \Pr[E_\Ec]
                           = \d \cdot (1 - \negl(\l))
                           = \d - \negl(\l)
  $$
\end{block}

- By construction, this implies that either:
  - $\PCDLSuccinctCheck$ rejects, which we show below is not the case, so:
  - The group element $U_j$ is not a commitment to $h_j(X)$.

- Since $\ASDLVerifier^{\rho_1}((q_{\acc_{i-1}} \cat \vec{q}), \acc_i)$ accepts,
  then, by construction:

  1. For each $j \in [m]$, $\PCDLSuccinctCheck$ accepts.
  2. Parsing $\acc_i = (C_\acc, d_\acc, z_\acc, v_\acc)$ and setting $\a := \rho_1([(h_j(X), U_j)]^m)$:
      - $z_\acc = \rho_1(C_\acc, [h_j(X)]^m)$
      - $C_\acc = \sum_{j=1}^m \a^j U_j, \; \; v_\acc = \sum_{j=1}^m \a^j h_j(z)$

## Proving $\AS$ Soundness (6/6): The Adversaries $\Bc_1, \Bc_2$

\begin{algorithm}[H]
\caption*{\textbf{The Adversary} $\Bc_k^{\rho_1}(\pp_\AS)$}
\begin{algorithmic}[1]
  \State Compute $(D, \acc_i, \vec{q}) \leftarrow \Cc^{\rho_1}(\pp_\AS)$, $p \leftarrow \Ec_\Cc^\rho(\pp_\AS)$.
  \State For each $q_j \in \vec{q}$ : $(h_j, U_j) \from \PCDLSuccinctCheck(q_j)$.
  \State Compute $\a := \rho_1([(h_j, U_j)]^m)$.
  \State \textbf{If} $k = a$ \textbf{Then} Output $((n, D), (p, h := ([h_j]^m)))$
  \State \textbf{If} $k = b$ \textbf{Then} Output $((n, D), ([(h_j, U_j)]^m))$
\end{algorithmic}
\end{algorithm}

\vspace{-1.5em}

1. $C_\acc \neq \sum_{j=1}^m \a^j B_j$: Meaning that $\exists j \in [m] : U_j \neq B_j$.
    - Since $C_\acc$ is a commit to $p(X)$, $p(X) - h(X) \neq 0$, but $p(z_\acc) = h(z_\acc)$.
    - Thusly, $a(X) \neq 0$ and $a(z_\acc) = 0$.
    - Because $z_\acc = z_a$ is sampled using the RO, $\Bc_a$ wins against $\CM_a$.
2. $C = \sum_{j=1}^n \a^j B_j$. Meaning that $\forall j \in [m] : U_j = B_j$.
    - Since $C = \sum_{j=1}^n \a^j U_j$, $\a$ is a root of the polynomial $b(Z)$, $b(\a) = 0$.
    - $b(X) = b_jX$
    - Because $\a$ is sampled using the RO, $\Bc_b$ wins against $CM_b$
$\Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{ wins}] = \delta - \negl(\l), \Pr[\Bc_1 \text{ wins} \land \Bc_2 \text{ wins}] = 0$.

# $\AS$ Efficiency

### Analysis

- $\ASDLCommonSubroutine$:
  - Step 6: $m$ calls to $\PCDLSuccinctCheck$, $\Oc(2m\lg(d))$ scalar muls.
  - Step 11: $m$ scalar muls.

  Step 6 dominates with $\Oc(2m\lg(d)) = \Oc(m\lg(d))$ scalar muls.
- $\ASDLProver$:
  - Step 4: Call to $\ASDLCommonSubroutine$, $\Oc(md)$ scalar muls.
  - Step 5: Evaluation of $h(X)$, $\Oc(\lg(d))$ scalar muls.
  - Step 6: Call to $\PCDLOpen$, $\Oc(3d)$ scalar muls.

  Step 6 dominates with $\Oc(3d) = \Oc(d)$ scalar muls.
- $\ASDLVerifier$:
  - Step 2: Call to $\ASDLCommonSubroutine$, $\Oc(2m\lg(d))$ scalar muls.
- $\ASDLDecider$:
  - Step 2: Call to $\PCDLCheck$, with $\Oc(d)$ scalar muls.

\vspace{0.3em}

- So $\ASDLProver$ and $\ASDLDecider$ are linear and $\ASDLDecider$ is sub-linear.

<!-- TODO: steps -->

# IVC based on $\AS$

## Prerequisites test

- We assume we have an underlying NARK which proof consists of only instances
  $\pi \in \Proof = [\vec{q}]^m$. We assume this NARK has three algorithms:
  - $\NARKProver(R: \Circuit, x: \PublicInfo, w: \Witness) \to \Proof$
  - $\NARKVerifier(R: \Circuit, x: \PublicInfo, \pi: \Proof) \to \Result(\top, \bot)$
  - $\NARKVerifierFast(R: \Circuit, x: \PublicInfo, \pi: \Proof) \to \Result(\top, \bot)$

\centering
\begin{tikzpicture}[node distance=2cm]

  % Nodes
  \node (s0) [node] {$s_0$};
  \node (s1) [node, right=of s0] {$(s_1, \pi_1, \acc_1)$};
  \node (dots) [right=2.25cm of s1] {$\dots$};
  \node (sn) [node, right=0.5cm of dots] {$(s_n, \pi_n, \acc_n)$};

  % Arrows with labels
  \draw[thick-arrow] (s0) -- node[above] {$\Pc(s_0, \bot, \bot)$} (s1);
  \draw[thick-arrow] (s1) -- node[above] {$\Pc(s_1, \pi_1, \acc_1)$} (dots);
  \draw[thick-arrow] (dots) -- (sn);

\end{tikzpicture}

## The circuit visualized

- $x = \{ R_{IVC}, s_0, s_i, \acc_i \}$
- $w = \{ s_{i-1}, \pi_{i-1} = \vec{q}, \acc_{i-1} \}$

\centering
\begin{tikzpicture}
  % First Layer
  \node[draw, rectangle] (q) at (6, 6.5) {$\vec{q}$};
  \node[draw, rectangle] (acc_prev) at (7.5, 6.5) {$\acc_{i-1}$};
  \node[draw, rectangle] (acc_next) at (9, 6.5) {$\acc_i$};

  \node[draw, rectangle] (R_ivc) at (2.25, 6.5) {$R_{IVC}$};
  \node[draw, rectangle] (x_prev) at (3.5, 6.5) {$x_{i-1}$};
  \node[draw, rectangle] (pi_prev) at (4.75, 6.5) {$\pi_{i-1}$};

  \node[draw, rectangle] (s_next) at (-1.5, 6.5) {$s_i$};
  \node[draw, rectangle] (s_prev) at (-0.25, 6.5) {$s_{i-1}$};
  \node[draw, rectangle] (s_0) at (1, 6.5) {$s_0$};

  \draw[dashed-arrow] (pi_prev) -- (4.75, 7) -- (6, 7) -- (q);

  \draw[dashed-arrow] (R_ivc) -- (2.25, 7) -- (3.5, 7) -- (x_prev);
  \draw[dashed-arrow] (s_prev) -- (-0.25, 7.1) -- (3.5, 7.1) -- (x_prev);
  \draw[dashed-arrow] (acc_prev) -- (7.5, 7.2) -- (3.5, 7.2) -- (x_prev);

  % Second Layer
  \node[draw, rectangle] (svf) at (3.5, 5.5) {$\NARKVerifierFast$};
  \node[draw, rectangle] (asv) at (7.5, 5.5) {$\ASVerifier$};

  \draw[arrow] (R_ivc) -- (svf);
  \draw[arrow] (x_prev) -- (svf);
  \draw[arrow] (pi_prev) -- (svf);

  \draw[arrow] (q) -- (asv);
  \draw[arrow] (acc_prev) -- (asv);
  \draw[arrow] (acc_next) -- (asv);

  % Third Layer
  \node[draw, rectangle] (asv_svf_and) at (5.75, 4.5) {$\land$};
  \node[draw, rectangle] (base_case) at (1, 4.5) {$s_{i-1} \meq s_0$};

  \draw[arrow] (asv) -- (asv_svf_and);
  \draw[arrow] (svf) -- (asv_svf_and);

  \draw[arrow] (s_prev) -- (base_case);
  \draw[arrow] (s_0) -- (base_case);

  % Fourth Layer
  \node[draw, rectangle] (or) at (4, 3.5) {$\lor$};
  \node[draw, rectangle] (F) at (-1, 3.5) {$F(s_{i-1}) \meq s_i$};

  \draw[arrow] (asv_svf_and) -- (or);
  \draw[arrow] (base_case) -- (or);

  \draw[arrow] (s_next) -- (F);
  \draw[arrow] (s_prev) -- (F);

  % Fifth Layer
  \node[draw, rectangle] (end_and) at (3, 2.5) { $\land$ };
  \draw[arrow] (or) -- (end_and);
  \draw[arrow] (F) -- (end_and);

\end{tikzpicture}

## The IVC prover

\begin{algorithm}[H]
\caption*{\textbf{Algorithm} $\IVCProver$}
\textbf{Inputs} \\
  \Desc{$R_{IVC}: \Circuit$}{The IVC circuit as defined above.} \\
  \Desc{$x: \PublicInputs$}{Public inputs for $R_{IVC}$.} \\
  \Desc{$w: \Option(\Witness)$}{Private inputs for $R_{IVC}$.} \\
\textbf{Output} \\
  \Desc{$(S, \Proof, \Acc)$}{The values for the next IVC iteration.}
\begin{algorithmic}[1]
  \Require $x = \{ s_0 \}, \; \; w = \{ s_{i-1}, \pi_{i-1}, \acc_{i-1} \} \lor w = \bot$
  \State \textbf{If} $w = \bot$ \textbf{Then} $w = \{ s_{i-1} = s_0 \}$ (base-case) \textbf{Else}:
    \State \algind Run the accumulation prover: $\acc_i = \ASProver(\pi_{i-1} = \vec{q}, \acc_{i-1})$.
    \State \algind Compute the next value: $s_i = F(s_{i-1})$.
    \State \algind Define $x' = x \cup \{ R_{IVC}, s_i, \acc_i \}$.
  \State Generate a NARK proof using $R_{IVC}$: $\pi_i = \NARKProver(R_{IVC}, x', w)$.
  \State Output $(s_i, \pi_i, \acc_i)$
\end{algorithmic}
\end{algorithm}

## The IVC Verifier

\begin{algorithm}[H]
\caption*{\textbf{Algorithm} $\IVCVerifier$}
\textbf{Inputs} \\
  \Desc{$R_{IVC}: \Circuit$}{The IVC circuit.} \\
  \Desc{$x: \PublicInputs$}{Public inputs for $R_{IVC}$.} \\
\textbf{Output} \\
  \Desc{$\Result(\top, \bot)$}{Returns $\top$ or $\bot$.}
\begin{algorithmic}[1]
  \Require $x = \{ s_0, s_i, \acc_i \}$
  \State Define $x' = x \cup \{ R_{IVC} \}$.
  \State Verify that the accumulation scheme decider accepts: $\top \meq \ASDecider(\acc_i)$.
  \State Verify the validity of the IVC proof: $\top \meq \NARKVerifier(R_{IVC}, x', \pi_i)$.
  \State If the above two checks pass, then output $\top$, else output $\bot$.
\end{algorithmic}
\end{algorithm}

## Why it works

$$
\begin{alignedat}[b]{2}
  &\IVCVerifier(R_{IVC}, x_n = \{ s_0, s_n, \acc_i \}, \pi_n) = \top           &&\then \\
  &\forall i \in [n], \forall q_j \in \pi_i = \vec{q} : \PCDLCheck(q_j) = \top &&\;\; \land \\
  &F(s_{n-1}) = s_n     \land (s_{n-1} = s_0 \lor ( \Vc_1 \land \Vc_2 ))       &&\then \\
  &\ASVerifier(\pi_{n-1}, \acc_{n-1}, \acc_n) = \top                           &&\;\; \land \\
  &\NARKVerifierFast(R_{IVC}, x_{n-1}, \pi_{n-1}) = \top                       &&\then \dots \\
  &F(s_0) = s_1 \land (s_0 = s_0 \lor ( \Vc_1 \land \Vc_2 ))                   &&\then \\
  &F(s_0) = s_1                                                                &&\then \\
\end{alignedat}
$$

1. $\forall i \in [2, n] : \ASVerifier(\pi_{i-1}, \acc_{i-1}, \acc_i) = \top$, i.e, all accumulators are accumulated correctly.
2. $\forall i \in [2, n] : \NARKVerifierFast(R_{IVC}, x_{i-1}, \pi_{i-1})$, i.e, all the proofs are valid.

## Efficiency Analysis

- The $\NARKProver$ runtime scales linearly with the $d$ ($\Oc(d)$)
- The $\NARKVerifierFast$ runtime scales logarithmically with $d$ ($\Oc(\lg(d))$)
- The $\NARKVerifier$ runtime scales linearly with the degree-bound $d$ ($\Oc(d)$)
- The $F$ runtime is less than $\Oc(d)$, since $|R_F| \approx d$

Then we can conclude:

- The runtime of $\IVCProver$ is:
  - Step 5: The cost of running $\ASDLProver$, $\Oc(d)$.
  - Step 6: The cost of computing $F$, $\Oc(F(x))$.
  - Step 7: The cost of running $\NARKProver$, $\Oc(d)$.

  Totalling $\Oc(F(x) + d)$. So $\Oc(d)$.
- The runtime of $\IVCVerifier$ is:
  - Step 2: The cost of running $\ASDLDecider$, $\Oc(d)$ scalar muls.
  - Step 3: The cost of running $\NARKVerifier$, $\Oc(d)$ scalar muls.

  Totalling $\Oc(2d)$. So $\Oc(d)$

Notice that although the runtime of $\IVCVerifier$ is linear, it scales
with $d$, _not_ $n$. So the cost of verifying does not scale with the number
of iterations.

# Conclusion & Benchmarks

## Benchmarks

\begin{figure}
\centering
  \begin{tikzpicture}[scale=0.85]
    \begin{axis}[
      title={Benchmark Times for 100 Iterations},
      xlabel={The maximum degree bound $d$, plus 1},
      ylabel={Time (s)},
      xtick=data,
      legend pos=north west,
      legend style={fill=GbBg00},
      ymajorgrids=true,
      grid style=dashed,
      symbolic x coords={512, 1024, 2048, 4096, 8196, 16384},
      enlarge x limits=0.2
    ]
    \addplot[color=GbBlueDk, mark=*] coordinates {(512, 0.941) (1024, 1.504) (2048, 2.558) (4096, 4.495) (8196, 8.372) (16384, 15.253)};
    \addplot[color=GbRedDk, mark=square*] coordinates {(512, 0.607) (1024, 0.662) (2048, 0.798) (4096, 1.014) (8196, 1.161) (16384, 1.648)};
    \legend {acc\_cmp\_s, acc\_cmp\_f}
    \end{axis}
  \end{tikzpicture}
\end{figure}

## Conclusion

### The project:
  - Learned a lot...
  - Implementing IVC is _hard_.
  - Benchmarks looks good, excited to see degree bound increase.
