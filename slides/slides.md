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

- _How can we verify $s_n = F^n(s_0)$ without re-executing the computation?_

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

### $\Pc(s_{i-1}, \pi_{i-1})$ represents:
  - $s_i = F(s_{i-1})$
  - $\pi_i = \SNARKProver(R, x = \{ s_0, s_i \}, w = \{ s_{i-1}, \pi_{i-1} \})$
  - $R := \text{I.K.} \; w = \{ \pi_{i-1}, s_{i-1} \} \; \text{ s.t. }$
    - $s_i \meq F(s_{i-1}) \; \land \; (s_{i-1} \meq s_0 \lor \Vc(R, x = \{ s_0, s_i \}, \pi_{i-1}))$

## Proof

- $R$ gives us a series of proofs of the claims:
$$
\begin{alignedat}{7}
  &\text{I.K.} \; w \; &&\text{ s.t. } \; &&s_n     &&= F(s_{n-1}) \; &&\land \; (s_{n-1} = s_0  &&\lor \Vc(R, x, \pi_{n-1}) = \top), \\
  &\text{I.K.} \; w \; &&\text{ s.t. } \; &&s_{n-1} &&= F(s_{n-2}) \; &&\land \; (s_{n-2} = s_0  &&\lor \Vc(R, x, \pi_{n-2}) = \top), \; \dots \\
  &\text{I.K.} \; w \; &&\text{ s.t. } \; &&s_1     &&= F(s_0)     \; &&\land \; (s_0 = s_0      &&\lor \Vc(R, x, \pi_0) = \top)
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

# PCS based on DL

## Polynomial Commitment Scheme

- $\PCDLSetup(\l, D)^{\rho_0} \to \pp_\PC$: $(S, D, H, \vec{G})$

- $\PCDLCommit(p: \Fb^{d'}_q[X], d: \Nb) \to \Eb(\Fb_q)$:

  Creates a Pedersen commit to $\vec{p}^{\text{(coeffs)}}$ of degree $d' \leq d$.

- $\PCDLOpen^{\rho_0}(p: \Fb^{d'}_q[X], C: \Eb(\Fb_q), d: \Nb, z: \Fb_q) \to \EvalProof$:

  _"I know degree $d' \leq d$ polynomial $p$ with commit $C$ s.t. $p(z) = v$"_

- $\PCDLSuccinctCheck^{\rho_0}(q: \Instance) \to \Result((\Fb^d_q[X], \Eb(\Fb_q)), \bot)$:

  Partially check $\pi$. The expensive part of the full check is deferred.

- $\PCDLCheck^{\rho_0}(q: \Instance) \to \Result(\top, \bot)$:

  The full check on $\pi$.
$$q: \Instance = (C: \Eb(\Fb_q), d: \Nb, z: \Fb_q, v: \Fb_q, \pi: \EvalProof)$$

## Notes on Checking Evaluation Proofs for $\PCDL$

\begin{block}{Verifying checks:}
  \vspace{0.5em}
  \centering
  \begin{enumerate}
    \item $\pi = \vec{L}, \vec{R}, U, c$
    \item $C_{lg(n)} \meq cU + ch(z) H' = c^{(0)}G^{(0)} + c^{(0)}z^{(0)} H'$
    \item $U \meq \CMCommit(\vec{G}, \vec{h}^{\text{(coeffs)}}) \meq \ip{\vec{G}}{\vec{h}^{\text{(coeffs)}}}$
  \end{enumerate}
  \vspace{0.5em}
\end{block}

- $\PCDLSuccinctCheck$ either rejects or accepts and returns:
  - $U$:
    - Represents $G^{(0)}$.
    - May be wrong!
  - $h(X) := \prod^{\lg(n)-1}_{i=0} (1 + \xi_{\lg(n) - i} X^{2^i})$:
    - Compression polynomial for $\vec{G} \to G^{(0)}, z \to z^{(0)}$.
    - Degree-d, $\Oc(\lg(d))$ evaluation time.

# $\AS$ based on DL

## Overview

### Generally

- $\ASSetup(\l) \to \pp_\AS$
- $\ASProver(\vec{q}: \Instance^m, acc_{i-1}: \Option(\Acc)) \to \Acc$
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
  \State Compute the tuple $(\bar{C}, d, z, \bar{h}(X)) := \ASDLCommonSubroutine(\vec{q})$.
  \State Generate the evaluation proof $\pi := \PCDLOpen(\bar{h}(X), \bar{C}, d, z)$.
  \State Finally, output the accumulator $\acc_i = (\bar{C}, d, z, v := \bar{h}(z), \pi)$.
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
    \State Parse $\acc_i$ as $(\bar{C}_\acc, d_\acc, z_\acc, v_\acc, \_)$
    \State Compute $(\bar{C}, d, z, \bar{h}(X)) := \ASDLCommonSubroutine(\vec{q})$
    \State Then check that $C_\acc \meq \bar{C}, d_\acc \meq d, z_\acc \meq z$, and $v_\acc \meq \bar{h}(z)$.
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
    \State Check $\top \meq \PCDLCheck(\acc_i)$
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
  \For{$q_j \in \vec{q}$}
    \State Parse $d_j$ from $q_j$.
    \State Compute $(h_j(X), U_j) := \PCDLSuccinctCheck^{\rho_0}(q_j)$.
    \State Check that $d_j \meq d$
  \EndFor
  \State Compute the challenge $\a := \rho_1(\vec{h}, \vec{U})$
  \State Linearize $h_j, U_j$: $\bar{h}(X) := \sum^m_{j=1} \a^j h_j(X)$, $\bar{C} := \sum^m_{j=1} \a^j U_j$
  \State Compute: $z := \rho_1(\bar{C}, \bar{h}(X))$
  \State Output $(\bar{C}, d, z, \bar{h}(X))$.
\end{algorithmic}
\end{algorithm}

# $\AS$ Properties

## $\AS$ Completeness

Assuming that $\PCDL$ is complete.

- $\ASDLVerifier$:
  - Runs the same deterministic $\ASDLCommonSubroutine$ with the same inputs.
  - Given that $\ASDLProver$ is honest, $\ASDLVerifier$ will get the same outputs.
  - These are checked to be equal to the ones from $\acc_i$.
  - Therefore $\ASDLVerifier$ accepts with probability 1.

- $\ASDLDecider$:
  - Runs $\PCDLCheck$ on the $\acc_i$, representing an evaluation proof (instance).
  - The prover constructed the $\acc_i$ honestly.
  - Therefore this check will pass with probability 1.

## $\AS$ Soundness

- $\ASDLVerifier$ shows that $\bar{h}(X), \bar{C}$ are linear combinations of $h_j(X), U_j$'s.
- $\ASDLDecider$ shows that $\bar{C} = \PCDLCommit(\bar{h}(X), d)$, checks all $U_j$'s.
  - Let $\acc_i = (\bar{C}, d, z, v, \pi)$
  - $\PCDLCheck$ shows that $\bar{C}$ is a commitment to $\bar{h}'(X)$ and $\bar{h}'(z) = v$.
  - $\ASDLVerifier$ shows that $\bar{C} = \sum_{j=1}^m \a^j U_j$, $\bar{h}(z) = v$.
  - Since $v = \bar{h}(z) = \bar{h}'(z)$ then $\bar{h}(X) = \bar{h}'(X)$ with $1 - \Pr[d/|\Fb_q|]$.
  - Define $\forall j \in [m] : B_j = \ip{\vec{G}}{\vec{h_j}^{(\text{coeffs})}}$. If $\exists j \in [m]$ $B_j \neq U_j$ then:
    - $U_j$ is not a valid commitment to $h_j(X)$ and,
    - $\sum_{j=1}^m \a^j B_j \neq \sum_{j=1}^m \a^j U_j$

    As such $\bar{C}$ will not be a valid commitment to $\bar{h}(X)$. Unless,
  - $\a := \rho_1(\vec{h}, \vec{U})$ or $z = \rho_1(\bar{C}, \bar{h}(X))$ is constructed maliciously.
- Previous accumulators are instances, as such, they will also be checked.
- More formal argument in the report.

## $\AS$ Efficiency

\begin{block}{Analysis}
  \begin{itemize}
    \item $\ASDLCommonSubroutine$:
    \begin{itemize}
      \item Step 4: $m$ calls to $\PCDLSuccinctCheck$, $\Oc(m\lg(d))$ scalar muls.
      \item Step 8: $m\lg(d)$ field muls.
      \item Step 8: $m$ scalar muls.
    \end{itemize}
    Step 4 dominates with $\Oc(m\lg(d))$ scalar muls.
  \end{itemize}
  \begin{itemize}
    \item $\ASDLProver$:
    \begin{itemize}
      \item Step 1: Call to $\ASDLCommonSubroutine$, $\Oc(m\lg(d))$ scalar muls.
      \item Step 2: Call to $\PCDLOpen$, $\Oc(d)$ scalar muls.
      \item Step 3: Evaluation of $\bar{h}(X)$, $\Oc(m\lg(d))$ field muls.
    \end{itemize}
    Step 2 dominates with $\Oc(d)$ scalar muls.
  \end{itemize}
  \begin{itemize}
    \item $\ASDLVerifier$:
    \begin{itemize}
      \item Step 2: Call to $\ASDLCommonSubroutine$, $\Oc(m\lg(d))$ scalar muls.
    \end{itemize}
  \end{itemize}
  \begin{itemize}
    \item $\ASDLDecider$:
    \begin{itemize}
      \item Step 1: Call to $\PCDLCheck$, with $\Oc(d)$ scalar muls.
    \end{itemize}
  \end{itemize}
\end{block}

So $\ASDLProver, \ASDLDecider$ are linear and $\ASDLVerifier$ is sub-linear.

# IVC based on $\AS$

## Assuming a Nark

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

## The Circuit Visualized

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
  \State \textbf{If} (base-case) \textbf{Then} $\dots$ \textbf{Else}
  \State Run the accumulation prover: $\acc_i = \ASProver(\pi_{i-1} = \vec{q}, \acc_{i-1})$.
  \State Compute the next value: $s_i = F(s_{i-1})$.
  \State Define $x' = x \cup \{ R_{IVC}, s_i, \acc_i \}$.
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

## Why Does it Work?

$$
\begin{alignedat}[b]{2}
  &\IVCVerifier(R_{IVC}, x_n = \{ s_0, s_n, \acc_i \}, \pi_n) = \top           &&\then \\
  &\forall i \in [n], \forall q_j \in \pi_i = \vec{q} : \PCDLCheck(q_j) = \top &&\;\; \land \\
  &F(s_{n-1}) = s_n     \land (s_{n-1} = s_0 \lor ( \Vc_1 \land \Vc_2 ))       &&\then \\
  &\ASVerifier(\vec{q} = \pi_{n-1}, \acc_{n-1}, \acc_n) = \top                 &&\;\; \land \\
  &\NARKVerifierFast(R_{IVC}, x_{n-1}, \pi_{n-1}) = \top                       &&\then \dots \\
  &F(s_0) = s_1 \land (s_0 = s_0 \lor ( \Vc_1 \land \Vc_2 ))                   &&\then \\
  &F(s_0) = s_1                                                                &&\then \\
\end{alignedat}
$$

1. $\forall i \in [2, n] : \ASVerifier(\pi_{i-1}, \acc_{i-1}, \acc_i) = \top$, i.e, all accumulators are valid.
2. $\forall i \in [2, n] : \NARKVerifierFast(R_{IVC}, x_{i-1}, \pi_{i-1})$, i.e, all the proofs are valid.

## Efficiency Analysis

\begin{block}{Assumptions}
  \begin{itemize}
    \item $\NARKProver$ runtime scales linearly with $d$ ($\Oc(d)$)
    \item $\NARKVerifier$ runtime scales linearly with $d$ ($\Oc(d)$)
    \item $\NARKVerifierFast$ runtime scales sub-linearly with $d$ ($\Oc(\lg(d))$)
    \item $F$ runtime is less than $\Oc(d)$, since $|R_F| \lessapprox d$
  \end{itemize}
\end{block}

\begin{block}{Analysis}
  \begin{itemize}
    \item $\IVCProver$:
    \begin{itemize}
      \item Step 2: The cost of running $\ASDLProver$, $\Oc(d)$.
      \item Step 3: The cost of computing $F$, $\Oc(F(x))$.
      \item Step 5: The cost of running $\NARKProver$, $\Oc(d)$.
    \end{itemize}
    Totalling $\Oc(d)$.
  \end{itemize}
  \begin{itemize}
    \item $\IVCVerifier$:
    \begin{itemize}
      \item Step 2: The cost of running $\ASDLDecider$, $\Oc(d)$ scalar muls.
      \item Step 3: The cost of running $\NARKVerifier$, $\Oc(d)$ scalar muls.
    \end{itemize}
    Totalling $\Oc(d)$
  \end{itemize}
\end{block}

Although the runtime of $\IVCVerifier$ is linear, it scales with $d$,
**not** $n$.

# Benchmarks & Conclusion

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
    \legend {$\PCDLCheck$, $\ASDLVerifier$}
    \end{axis}
  \end{tikzpicture}
\end{figure}

## Conclusion

### The project:
  - Gained a deeper understanding of advanced cryptographic theory.
  - Learned to better carry theory into practice.
  - Implementing full IVC is _hard_.
  - Benchmarks looks good, excited to see degree bound increase.
  - Future work...
