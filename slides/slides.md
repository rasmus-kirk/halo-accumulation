---
title: Proving Type Preservation of $\beta$-reduction in System F
author:
  - Rasmus Kirk Jakobsen
theme: Berlin
date: 2024-01-08
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

- IVC is designed to solve the following problem

\vspace{0.6em}

\begin{quote}
\color{Gray}
If a computation runs for hundreds of years and ultimately outputs 42, how can
we check its correctness without re-executing the entire process?
\end{quote}

- We define the transition function $F$ run on an initial state $s_0$:

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

- How can we verify $F^n(s_0)$ without re-executing the computation?

## IVC chain

- We can use a SNARK to prove each computation step:

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

- $\Pc(s_i, \pi_i)$ represents:
  - $R := \text{I.K.} \; w = \{ \pi_{i-1}, s_{i-1} \} \; \text{ s.t. }$
    $$s_i \meq F(s_{i-1}) \; \land \; (s_{i-1} \meq s_0 \lor \Vc(R_F, x = \{ s_0, s_i \}, \pi_{i-1}))$$
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

# Accumulation Scheme based on the Discrete Log assumption

## In general

- $\ASSetup(\l) \to \pp_\AS$
- $\ASProver(\vec{q}: \Instance^m, acc_{i-1}: \Acc) \to \Acc$
- $\ASVerifier(\vec{q}: \Instance^m, acc_{i-1}: \Option(\Acc), acc_i: \Acc) \to \Result(\top, \bot)$
- $\ASDecider(acc_i: \Acc) \to \Result(\top, \bot)$

## $\ASDL$

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

## Completeness proof

$\ASDLVerifier$ runs the same algorithm ($\ASDLCommonSubroutine$) with the
same inputs and, given that $\ASDLProver$ is honest, will therefore get the
same outputs, these outputs are checked to be equal to the ones received from
the prover. Since these were generated honestly by the prover, also using
$\ASDLCommonSubroutine$, the $\ASDLVerifier$ will accept with probability 1,
returning $\top$. Intuitively, this also makes sense. It's the job of the
verifier to verify that each instance is accumulated correctly into the
accumulator. This verifier does the same work as the prover and checks that
the output matches.

As for the $\ASDLDecider$, it just runs $\PCDLCheck$ on the provided
accumulator, which represents a evaluation proof i.e. an instance. This
check will always pass, as the prover constructed it honestly.

## Soundness proof (1/?)

Let $\CM = (\CMSetup, \CMCommit)$ be a perfectly binding commitment scheme. Fix
a maximum degree $D \in \Nb$ and a random oracle $\rho$ that takes commitments
from $\CM$ to $F_\pp$. Then for every family of functions $\{f_\pp\}_\pp$
and fields $\{F_\pp\}_\pp$ where:

- $f_\pp \in \Mc \to F_\pp^{\leq D}[X]$
- $F \in \Nb \to \Nb$
- $|F_\pp| \geq F(\l)$

That is, for all functions, $f_\pp$, that takes a message, $\Mc$ as input and
outputs a maximum D-degree polynomial. Also, usually $|F_\pp| \approx F(\l)$.
For every message format $L$ and computationally unbounded $t$-query oracle
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

## Soundness proof (1/?)

$$
\Pr \left[
  \begin{array}{c}
    \ASDLVerifier^{\rho_1}((q_{\acc_{i-1}} \cat \vec{q}), \acc_i) = \top, \\
    \ASDLDecider^{\rho_1}(\acc_i) = \top \\
    \land \\
    \exists i \in [n] : \Phi_\AS(q_i) = \bot
  \end{array}
\right] \leq \negl(\l)
$$
Given:
$$
\begin{alignedat}{4}
  &\rho_0 &&\leftarrow \Uc(\l),                                               &&\quad \rho_1  &&\leftarrow \Uc(\l), \\
  &\pp_\PC &&\leftarrow \PCDLSetup^{\rho_0}(1^\l, D),                         &&\quad \pp_\AS &&\leftarrow \ASDLSetup^{\rho_1}(1^\l, \pp_\PC), \\
  &(\vec{q}, \acc_{i-1}, \acc_i) &&\leftarrow \Ac^{\rho_1}(\pp_\AS, \pp_\PC), &&\quad q_{acc_{i-1}} &&\leftarrow \ToInstance(\acc_{i-1})
\end{alignedat}
$$

- We call the probability that the adversary $\Ac$ wins the above game
  $\d$. We bound $\d$ by constructing two adversaries, $\Bc_1, \Bc_2$, for
  the zero-finding game. Assuming:
  - $\Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{wins}] = \delta - \negl(\l)$
  - $\Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{wins}] = 0$

## Soundness Proof (3/?)


$$
\begin{aligned}
  \Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{ wins}] &= \Pr[\Bc_1 \text{ wins}] + \Pr[\Bc_2\text{ wins}] - \Pr[\Bc_1 \text{ wins} \land \Bc_2 \text{ wins}]\\
  \Pr[\Bc_1 \text{ wins} \lor \Bc_2 \text{ wins}] &= \Pr[\Bc_1 \text{ wins}] + \Pr[\Bc_2\text{ wins}] - 0 \\
  \delta - \negl(\l)                              &\leq  \sqrt{\frac{D(t+1)}{F(\l)}} + \sqrt{\frac{D(t+1)}{F(\l)}} \\
  \delta - \negl(\l)                              &\leq  2 \cdot \sqrt{\frac{D(t+1)}{|\Fb_q|}}                     \\
  \delta                                          &\leq  2 \cdot \sqrt{\frac{D(t+1)}{|\Fb_q|}} + \negl(\l)         \\
\end{aligned}
$$

Meaning that $\delta$ is negligible, since $q = |\Fb_q|$ is superpolynomial
in $\l$.

## Soundness Proof (3/?)

## Efficiency analysis

## Accumulation Scheme IVC

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
