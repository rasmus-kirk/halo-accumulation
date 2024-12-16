---
title: Investigating IVC with Halo2
date: \today
author: 
  - Rasmus Kirk Jakobsen - 201907084
geometry: margin=1.75cm
---

\tableofcontents

# Introduction

Halo2, can be broken down into the following components:

- **Plonk**: A general-purpose zero-knowledge proof scheme.
- **$\PCDL$**: A Polynomial Commitment Scheme in the Discrete Log setting.
- **$\ASDL$**: An Accumulation Scheme in the Discrete Log setting.
- **Pasta**: A Cycle of Elliptic Curves, namely **Pa**llas and Ve**sta**.

This project is focused on the components of $\PCDL$ and $\ASDL$. I used the
[2020 paper](https://example.com) _"Proof-Carrying Data from Accumulation
Schemes"_ as a reference. The project covers both the theoretical aspects
of the scheme described in this document along with a rust implementation,
both of which can be found in the project's [repository](https://example.com).

The original paper had additional functions for generating prover and
verifier keys, getting the public parameters and trimming input to fit the
public parameters. I have chosen to omit these from the discussion below as
these are fixed per-implementation.

# Prerequisites

Basic knowledge on elliptic curves, groups, interactive arguments are
assumed in the following text. There is also a heavy reliance on the Inner
Product Proof from the Bulletproofs protocol, see the following resources
on bulletproofs if need be:

- [Section 3 in the original Bulletproofs paper](https://eprint.iacr.org/2017/1066.pdf#section.3)
- [From Zero (Knowledge) to Bulletproofs writeup](https://github.com/AdamISZ/from0k2bp/blob/master/from0k2bp.pdf)
- [Rust Dalek Bulletproofs implementation notes](https://doc-internal.dalek.rs/develop/bulletproofs/notes/inner_product_proof/)
- [Section 4.1 of my bachelors thesis](https://rasmuskirk.com/documents/high-assurance-cryptography-implementing-bulletproofs-in-hacspec.pdf#subsection.4.1)

# $\PCDL$: The Polynomial Commitment Scheme

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

We can further group these terms:

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

And then simplify further:

$$
\begin{alignedat}[b]{1}
  \vec{L}    &= (L_0, \dots, L_{\lg(n)-1}) \\
  \vec{R}    &= (R_0, \dots, R_{\lg(n)-1}) \\
  \vec{C}    &= (C_0, \dots, C_{\lg(n)}) \\
  \vec{\xi}  &= (\xi_0, \dots, \xi_{\lg(n)}) \\
\end{alignedat}
$$

Now we are ready to look at the check that the verifier makes:

\begin{align*}
  C_0        &= \bar{C} + vH' = C + vH' && \\
  C_{\lg(n)} &= C_0 + \sum^{\lg(n)-1}_{i=0} \xi^{-1}_{i+1} L_i + \xi_{i+1} R_i && \\
             \intertext{The original definition of $C_i$:}
             &= \ip{\vec{c}_{\lg(n)}}{\vec{G}_{\lg(n)}} + \ip{\vec{c}_{\lg(n)}}{\vec{z}_{\lg(n)}} H' \\
             \intertext{Vectors have length one, use the single elements $c^{(0)}, G^{(0)}, c^{(0)}, z^{(0)}$:}
             &= c^{(0)}G^{(0)} + c^{(0)}z^{(0)} H'                                                   \\
             \intertext{The verifier has $c^{(0)} = c, G^{(0)} = U$ from $\pi \in \textbf{EvalProof}$:}
             &= cU + cz^{(0)} H'                                                                     \\
             \intertext{And finally, by construction of $h(X) \in \Fb^d_q[X]$}
             &= cU + ch(z) H'                                                                        \\
\end{align*}
Which corresponds exactly to the check that the verifier makes.

## Outline

We have four main functions:

- $\PCDLdot{Commit}(p: \Fb^d_q[X], \o: \textbf{Option}(\Fb_q)) \to \Eb(\Fb_q)$:

  Creates a commitment to the coefficients of the polynomial $q$ of degree
  $d$ with optional hiding $\o$, using pedersen commitments.

- $\PCDLdot{Open}(p: \Fb^d_q[X], C: \Eb(\Fb_q), z: \Fb_q, \o: \textbf{Option}(\Fb_q)) \to \pi_{\textsc{eval}}$:

  Creates a proof $\pi$ that states: "I know $p \in \Fb^d_q[X]$ with
  commitment $C \in \Eb(\Fb_q)$ s.t. $p(z) = v$" where $p$ is private
  and $d, z, v$ are public.

- $\PCDLdot{SuccinctCheck}(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \pi_{\textsc{eval}}) \to \textbf{Result}(\Fb^d_q[X], \Gb)$:

  Cheaply checks that a proof $\pi$ is correct. It is not a full check however,
  since an expensive part of the check is deferred until a later point.

- $\PCDLdot{Check}(C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \pi_{\textsc{eval}}) \to \textbf{Result}(\top, \bot)$:

  The full check on $\pi$.

### $\PCDLdot{Commit}$

$\PCDLdot{Commit}$ is rather simple, we just take the coefficients of the polynomial and
commit to them using a pedersen commitment:

\begin{algorithm}[H]
\caption{$\PCDLdot{Commit}$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$p: \Fb^d_q[X]$}{The univariate polynomial that we wish to commit to.} \\
  \Desc{$\mathcolor{GbBlueDk}{\o}: \textbf{Option}(\Fb_q)$}{Optional hiding factor for the commitment.} \\
\textbf{Output} \\
  \Desc{$C: \Eb(\Fb_q)$}{The pedersen commitment to the coefficients of polynomial $p$.}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Let $\vec{p}$ be the coefficient vector for $p$
  \State Output $C := \textsc{CM.Commit}(\vec{G}, \vec{p}, \mathcolor{GbBlueDk}{\o})$.
\end{algorithmic}
\end{algorithm}

### $\PCDLdot{Open}$

\begin{algorithm}[H]
\caption{$\PCDLdot{Open}$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$p: \Fb^d_q[X]$}{The univariate polynomial that we wish to open for.} \\
  \Desc{$C: \Eb(\Fb_q$)}{A commitment to the coefficients of $p$.} \\
  \Desc{$z: \Fb_q$}{The element that $z$ will be evaluated on $v = p(z)$.} \\
  \Desc{$\mathcolor{GbBlueDk}{\o}: \textbf{Option}(\Fb_q)$}{Optional hiding factor for $C$. \textit{Must} be included if $C$ was created with hiding!} \\
\textbf{Output} \\
  \Desc{$\mathbf{EvalProof}$}{Proof that states: "I know $p \in \Fb^d_q[X]$ with commitment $C \in \Eb(\Fb_q)$ s.t. $p(z) = v$"}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Compute $v = p(z)$ and let $n = d+1$.
  \State \textcolor{GbBlueDk}{Sample a random polynomial $\bar{p} \in \Fb^{\leq d}_q[X]$ such that $\bar{p}(z) = 0$}.
  \State \textcolor{GbBlueDk}{Sample corresponding commitment randomness $\bar{\o} \in \Fb_q$.}
  \State \textcolor{GbBlueDk}{Compute a hiding commitment to $\bar{p}$: $\bar{C} \gets \textsc{CM.Commit}(\vec{G}, \bar{p}, \bar{\o}) \in \Gb$.}
  \State \textcolor{GbBlueDk}{Compute the challenge $\a := \rho_0(C, z, v, \bar{C}) \in \Fb^{*}_q$.}
  \State Compute the polynomial $p' := p \mathcolor{GbBlueDk}{+ \a \bar{p}} = \sum_{i=0} c_i X_i \in \Fb_q[X]$.
  \State Compute commitment randomness $\o' := \o + \a \bar{\o} \in \Fb_q$.
  \State Compute a non-hiding commitment to $p'$: $C' := C \mathcolor{GbBlueDk}{+ \a \bar{C} - \o' S} \in \Gb$.
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
    \State Compute $L_i := \textsc{CM.Commit}(l(\vec{G_{i-1}}) \cat H', \; \;  r(\vec{c_{i-1}}) \cat \langle r(\vec{c_{i-1}}), l(\vec{z_{i-1}}) \rangle, \; \; \bot)$
    \State Compute $R_i := \textsc{CM.Commit}(r(\vec{G_{i-1}}) \cat H', \; \; l(\vec{c_{i-1}}) \cat \langle l(\vec{c_{i-1}}), r(\vec{z_{i-1}}) \rangle, \; \; \bot)$
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
  \State Finally output the evaluation proof $\pi := (\vec{L},\vec{R}, U := \vec{G}_{lg(n)}, c := \vec{c}_{lg(n)}, \mathcolor{GbBlueDk}{\bar{C}, \o'})$
\end{algorithmic}
\end{algorithm}

The $\PCDLdot{Open}$ algorithm simply follows the proving algorithm from
bulletproofs. Except,in this case we are trying to prove we know polynomial
$p$ s.t. $v = \dotp{\vec{c_0}}{\vec{z_0}}$. So because $z$ is public, we
can get away with omitting the generators for $\vec{b}$ in the original protocol $(\vec{H})$.

### $\PCDLdot{SuccinctCheck}$

\begin{algorithm}[H]
\caption{$\PCDLdot{SuccinctCheck}$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$C: \Eb(\Fb_q)$}{A commitment to the coefficients of $p$.} \\
  \Desc{$d: \Nb$}{The degree of $p$} \\
  \Desc{$z: \Fb_q$}{The element that $p$ is evaluated on.} \\
  \Desc{$v: \Fb_q$}{The claimed element $v = p(z)$.} \\
  \Desc{$\pi: \textbf{EvalProof}$}{The evaluation proof produced by $\PCDLdot{Open}$} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}((\Fb^d_q[X], \Gb), \bot)$}{The algorithm will either succeed and output ($h: \Fb^d_q[X], U: \Gb$) if $\pi$ is a valid proof and otherwise fail ($\bot$).}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Parse $\pi$ as $(\vec{L},\vec{R}, U := \vec{G}_{lg(n)}, c := \vec{c}_{lg(n)}, \mathcolor{GbBlueDk}{\bar{C}, \o'})$ and let $n = d + 1$.
  \State \textcolor{GbBlueDk}{Compute the challenge $\alpha := \rho_0(C, z, v, \bar{C}) \in F^{*}_q$.}
  \State Compute the non-hiding commitment $C' := C \mathcolor{GbBlueDk}{+ \a \bar{C} - \o'S} \in \Gb$.
  \State Compute the 0-th challenge: $\xi_0 := \rho_0(C', z, v)$, and set $H' := \xi_0 H \in \Gb$.
  \State Compute the group element $C_0 := C' + vH' \in \Gb$.
  \For{$i \in [\lg(n)]$}
    \State Generate the i-th challenge: $\xi_i := \rho_0(\xi_{i-1}, L_i, R_i) \in \Fb_q$.
    \State Compute the i-th commitment: $C_i := \xi^{-1}_i L_i + C_{i-1} + \xi_i R_i \in \Gb$.
  \EndFor
\State Define the univariate polynomial $h(X) := \prod^{\lg(n)-1}_{i=0} (1 + \xi_{\lg(n) - i} X^{2^i}) \in \Fb_q[X]$.
\State Compute the evaluation $v' := c \cdot h(z) \in \Fb_q$.
\State Check that $C_{lg(n)} \meq \textsc{CM.Commit}(U \cat H', c \cat v', \bot)$
\State Output (h(X), U).
\end{algorithmic}
\end{algorithm}

### $\PCDLdot{Check}$

\begin{algorithm}[H]
\caption{$\PCDLdot{Check}$}\label{alg:cap}
\textbf{Inputs} \\
  \Desc{$C: \Eb(\Fb_q)$}{A commitment to the coefficients of $p$.} \\
  \Desc{$d: \Nb$}{The degree of $p$} \\
  \Desc{$z: \Fb_q$}{The element that $p$ is evaluated on.} \\
  \Desc{$v: \Fb_q$}{The claimed element $v = p(z)$.} \\
  \Desc{$\pi: \mathbf{EvalProof}$}{The evaluation proof produced by $\PCDLdot{Open}$} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}(\top, \bot)$}{The algorithm will either succeed ($\top$) if $\pi$ is a valid proof and otherwise fail ($\bot$).}
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Check that $\PCDLdot{SuccinctCheck}(C, d, z, v, \pi)$ accepts and outputs $(h, U)$.
  \State Check that $U \meq \textsc{CM.Commit}(\vec{G}, \vec{h}, \bot)$, where $\vec{h}$ is the coefficient vector of the polynomial $h$.
\end{algorithmic}
\end{algorithm}

## Completeness

This section will both function as an explainer of what is going on in this
algorithm, along with a more formal proof of completeness.

## Soundness

## Zero-knowledge

## Benchmarks

# $\ASDL$: The Accumulation Scheme

## Common subroutine

\begin{algorithm}[H]
\caption{$\ASDLdot{CommonSubroutine}$}
\textbf{Inputs} \\
  \Desc{$d: \Nb$}{The degree of $p$.} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
  \Desc{$\mathcolor{GbBlueDk}{\pi_V}: \Option(\textbf{AccHiding})$}{Necessary parameters if hiding is desired.} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}((\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X]), \bot)$}{
    The algorithm will either succeed $(\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q[X])$
    if the instances has consistent degree and hiding parameters and otherwise
    fail ($\bot$).
  }
\begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \For{$i \in [m]$}
    \State Parse $q_i$ as a tuple $((C_i, d_i, z_i, v_i), \pi_i)$.
    \State Compute $(h_i(X), U_i) := \PCDLdot(C_i, z_i, v_i, \pi_i)$.
    \State Check that $d_i = D$ (We accumulate only the degree bound D.)
  \EndFor
  \State \textcolor{GbBlueDk}{Parse $\pi_V$ as $(h_0, U_0, \o)$, where $h_0(X) = aX + b \in \Fb^1_q[X], U_0 \in \Gb$ and $\o \in \Fb_q$}
  \State \textcolor{GbBlueDk}{Check that $U_0$ is a deterministic commitment to $h_0$: $U_0 = \PCDLdot{Commit}(h, \bot)$.}
  \State Compute the challenge $\a := \rho_1(\vec{h}, \vec{U}) \in \Fb_q$
  \State Let the polynomial $h(X) := \sum^m_{i=0} \a^i h_i \in \Fb_q[X]$
  \State Compute the accumulated commitment $C := \sum^m_{i=0} \a^i U_i$
  \State Compute the challenge $z := \rho_1(C, h) \in \Fb_q$.
  \State Randomize $C$: $\bar{C} := C \mathcolor{GbBlueDk}{+ \o S} \in \Gb$.
  \State Output $(\bar{C}, d, z, h(X))$.
\end{algorithmic}
\end{algorithm}

## Prover

\begin{algorithm}[H]
\caption{$\ASDLdot{Prover}$}
\textbf{Inputs} \\
  \Desc{$d: \Nb$}{The degree of $p$.} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}(\textbf{Acc}, \bot)$}{
    The algorithm will either succeed $((\bar{C}, d, z, v, \pi), \pi_V)
    \in \textbf{Acc})$ if the instances has consistent degree and hiding
    parameters and otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $d \leq D$
  \Require $(d+1) = 2^k$, where $k \in \Nb$
  \State Let $n = d + 1$
  \State Sample a random linear polynomial $h_0 \in F_q[X]$
  \State Then compute a deterministic commitment to $h_0$: $U_0 := \PCDLdot{Commit}(h_0, \bot)$
  \State \textcolor{GbBlueDk}{Sample commitment randomness $\o \in F_q$, and set $\pi_V := (h_0, U_0, \o)$.}
  \State Then, compute the tuple $(\bar{C}, d, z, h(X)) := \ASDLdot{CommonSubroutine}(d, \vec{q} \mathcolor{GbBlueDk}{, \pi_V})$.
  \State Compute the evaluation $v := h(z)$
  \State Generate the hiding evaluation proof $\pi := \PCDLdot{Open}(h(X), \bar{C}, d, z \mathcolor{GbBlueDk}{, \o})$.
  \State Finally, output the accumulator $acc = ((\bar{C}, d, z, v, \pi), \pi_V)$.
\end{algorithmic}
\end{algorithm}

## Verifier

\begin{algorithm}[H]
\caption{$\ASDLdot{Verifier}$}
\textbf{Inputs} \\
  \Desc{$\vec{q}: \Fb_q^m$}{New instances \textit{and accumulators} to be accumulated.} \\
  \Desc{$acc: \textbf{Acc}$}{The accumulator.} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}(\top, \bot)$}{
    The algorithm will either succeed $(\top)$ if TODO and otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $acc.d \leq D$
  \Require $(acc.d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $acc$ as $((\bar{C}, d, z, v, \_) \mathcolor{GbBlueDk}{, \pi_V})$
    \State The accumulation verifier computes $(\bar{C}', d', z', h(X)) := \ASDLdot{CommonSubroutine}(d, \vec{q} \mathcolor{GbBlueDk}{, \pi_V})$
    \State Then checks that $\bar{C}' \meq \bar{C}, d' \meq d, z' \meq z$, and $h(z) \meq v$.
\end{algorithmic}
\end{algorithm}

## Decider

\begin{algorithm}[H]
\caption{$\ASDLdot{Decider}$}
\textbf{Inputs} \\
  \Desc{$acc: \textbf{Acc}$}{The accumulator.} \\
\textbf{Output} \\
  \Desc{$\textbf{Result}(\top, \bot)$}{
    The algorithm will either succeed $(\top)$ if TODO and otherwise fail ($\bot$).
  }
  \begin{algorithmic}[1]
  \Require $acc.d \leq D$
  \Require $(acc.d+1) = 2^k$, where $k \in \Nb$ 
    \State Parse $acc$ as $((\bar{C}, d, z, v, \pi), \_)$
    \State Check $\top \meq \PCDLdot{Check}(\bar{C}, d, z, v, \pi)$
\end{algorithmic}
\end{algorithm}

## Completeness

## Soundness

## Zero-knowledge

## Benchmarks

\newpage

# Appendix

## Notation

$(\Fb_q, \dots, \Eb(\Fb_q))$: Same as $\Fb_q \times \dots \times \Eb(\Fb_q)$

$\dotp{\vec{a}}{\vec{G}}$ where $\vec{a} \in \Fb^n_q, \vec{G} \in \Eb^n(\Fb_q)$: The dot product of field elements $\vec{a}$ and curve points $\vec{G}$ ($\sum^n_{i=0} a_i G_i$).

$\dotp{\vec{a}}{\vec{b}}$ where $\vec{a} \in \Fb^n_q, \vec{b} \in \Fb^n_q$: The dot product of vectors $\vec{a}$ and $\vec{b}$.

$l(\vec{a})$: Gets the left half of $\vec{a}$.

$r(\vec{a})$: Gets the right half of $\vec{a}$.

$\vec{a} \cat \vec{b}$ where $\vec{a} \in \Fb^n_q, \vec{b} \in \Fb^m_q$: Concatinate vectors to create $\vec{c} \in \Fb^{n+m}_q$.

$a \cat b$ where $a \in \Fb_q$: Create vector $\vec{c} = (a, b)$.

"Type aliases"

$\textbf{EvalProof} = (\Eb^{lg(n)}(\Fb_q), \Eb^{lg(n)}(\Fb_q), \Eb(\Fb_q), \Fb_q\mathcolor{GbBlueDk}{, \Eb(\Fb_q), \Fb_q})$

$\textbf{AccHiding} = (\Eb(\Fb_q), \Nb, \Fb_q, \Fb^d_q)$

$\textbf{Acc} = ((\Eb(\Fb_q), \Nb, \Fb_q, \Fb_q, \textbf{EvalProof}), \textbf{AccHiding})$


## $\textsc{CM}$: Pedersen Commitment

As a reference, we include the Pedersen Commitment algorithm we use:

\begin{algorithm}[H]
\caption{$\textsc{CM.Commit}$}
\textbf{Inputs} \\
  \Desc{$\vec{m}: \Fb^n$}{The vectors we wish to commit to.} \\
  \Desc{$\vec{G}: \Eb(\Fb)^n$}{The generators we use to create the commitment.} \\
  \Desc{$\mathcolor{GbBlueDk}{\o}: \textbf{Option}(\Fb_q)$}{Optional hiding factor for the commitment.} \\
\textbf{Output} \\
  \Desc{$C: \Eb(\Fb_q)$}{The pedersen commitment.}
\begin{algorithmic}[1]
  \State Output $C := \vec{m} \cdot \vec{G} \mathcolor{GbBlueDk}{+ \o S})$.
\end{algorithmic}
\end{algorithm}

```rust
pub fn commit(w: Option<&PallasScalar>, Gs: &[PallasAffine], ms: &[PallasScalar]) -> PallasPoint {
    assert!(
        Gs.len() == ms.len(),
        "Length did not match for pedersen commitment: {}, {}",
        Gs.len(),
        ms.len()
    );

    let acc = point_dot_affine(ms, Gs);
    if let Some(w) = w {
        S * w + acc
    } else {
        acc
    }
}
```

