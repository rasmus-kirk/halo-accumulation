---
geometry: margin=2cm
---

### Lemma 3.3

Let $F: \mathbb{N} \to \mathbb{N}$, and $\text{CM} = (\text{Setup}, \text{Trim}, \text{Commit})$ be a commitment scheme. Fix a number of variables $M \in \mathbb{N}$ and maximum degree $N \in \mathbb{N}$. Then for every family of (not necessarily efficient) functions $\{f_{pp}\}_{pp}$ and fields $\{\mathbb{F}_{pp}\}_{pp}$ where $f_{pp}: \mathcal{M}_{pp} \to \mathbb{F}^{\leq N}_{pp}[X_1, \ldots, X_M]$ and $|\mathbb{F}_{pp}| \geq F(\lambda)$; for every message format $L$ and efficient $t$-query oracle algorithm $A$, the following holds:

$$
\Pr\left[
\begin{array}{c}
p \not\equiv 0 \\
\land \, p(z) = 0
\end{array}
\middle|
\begin{array}{l}
pp \leftarrow \text{CM.Setup}(1^\lambda, L) \\
(\ell, p \in \mathcal{M}_{ck}, \omega) \leftarrow A^{\rho}(pp) \\
ck \leftarrow \text{CM.Trim}(pp, \ell) \\
C \leftarrow \text{CM.Commit}(ck, p; \omega) \\
z \in \mathbb{F}^{N}_{pp} \leftarrow \rho(C) \\
p \leftarrow f_{pp}(p)
\end{array}
\right]
\leq \sqrt{(t+1) \cdot \frac{MN}{F(\lambda)}} + \text{negl}(\lambda).
$$

If $\text{CM}$ is perfectly binding, then the above holds also for computationally-unbounded $t$-query adversaries $A$.

Similarly to the completeness case, we consider a simplified version of the
definition of soundness in Section 4. This simpler definition requires that the
following probability is negligible for every Polynomial-Size Adversary $\Ac$:

$$
\Pr \left[
  \begin{array}{c|c}
    \begin{array}{c}
      \Verifier^\rho([q_i]_{i=1}^n, \acc, \pi_V) = 1, \\
      \ASDecider^\rho(\acc) = 1 \\
      \wedge \\
      \exists i \in [n],
      \, \Phi^\rho_{\PC}(\pp_\PC, i_\phi, q_i) = 0
    \end{array}
  & \quad
    \begin{aligned}
      \rho &\leftarrow \Uc(\lambda), \\
      \pp &\leftarrow \ASGenerator^\rho(1^\lambda), \\
      \pp_\PC &\leftarrow \mathcal{H}_{\PC}^\rho(\pp), \\
      (i_\phi, [q_i]_{i=1}^n, \acc, \pi_V) &\leftarrow \Ac^\rho(\pp, \pp_{\PC}) \\
      (\text{apk}, \text{avk}, \text{dk}) &\leftarrow \mathcal{I}^\rho(\text{pp}, \text{pp}_{\text{PC}}, i_\phi)
    \end{aligned}
  \end{array}
\right]
$$

Fix a polynomial-size adversary $\Ac$ and degree bound $D$, and denote
by $\delta$ the above probability for these choices. We will construct an
adversary for the zero-finding game in Lemma 3.3 that wins with probability
$\delta / 2 - \text{negl}(\lambda)$, from which it follows that $\delta$
is negligible (since $q$ is superpolynomial in $\lambda$).

We first describe the commitment schemes $\CM_1, \CM_2$ used in
the zero-finding games. Both schemes have common setup and trimming
algorithms, and public parameters $\pp$ equal to the public
parameters of $\PCDL$ with maximum degree $L$. The message
space $\Mc_{\text{pp}}$ for $CM_1$ consists of tuples $(p,
h)$, where $p$ and $h$ are univariate polynomials of degree at most
$L$. Note that $h$ is uniquely represented by $[h_i]_{i=0}^n, \alpha$,
where each $h_i$ is a univariate polynomial of degree $L$, and $\alpha
\in \Fb_q$.

The message space $\Mc_\pp$ for $\CM_2$ consists of
lists of pairs $[(h_i, U_i)]_{i=0}^n$, where each $h_i$ is a univariate
polynomial of degree at most $L$, and each $U_i$ is a group element.

---

#### Algorithm:

1. $\CM_j.\Setup^{\rho}(1^\lambda, L)$:
   - Output: $\text{pp} \leftarrow \PCDLSetup^\rho(1^\lambda, L)$.

2. $\CM_j.\Trim^\rho(\text{pp}, n, N)$:
  - Compute $(\text{ck}_0, \text{rk}_0) \leftarrow \PCDLTrim^\rho(\text{pp}, N)$.
  - Output: $\text{ck} := (\text{ck}_0, n)$.

3. $\CM_1.\Commit(\text{ck} = (\text{ck}_0, n), p = (p, h); r)$:
   - Commit to $p$: $C \leftarrow \PCDLCommit(\text{ck}_0,
   p; \omega = \perp)$.  - Output: $(C, h)$.

4. $\CM_2.\Commit(\text{ck}, p = \{(h_i, U_i)\}_{i=0}^n; r)$:
   - Output: $p$.

---

Both commitment schemes are binding. It remains to specify the families of
functions $\{f^{(1)}_{\text{pp}}, f^{(2)}_{\text{pp}}\}$ that we use in
the respective zero-finding games.

We define: $f^{(1)}_{\text{pp}}(p, h = \{h_i\}_{i=0}^n) := p - \sum_{i} \alpha^i h_i,$

and: $f^{(2)}_{\text{pp}}(p = \{(h_i, U_i)\}_{i=0}^n):$

1. Construct the key pair $(\text{ck}_0, \text{rk}_0) = \PCDLTrim(\pp_\PC, \deg(h_i))$.
2. For each $i \in [0, \ldots, n]$, construct a $\PCDL$ commitment
   to $h_i$: $B_i \leftarrow \PCDLCommit(\text{ck}, h_i, \bot)$.
3. For each $i \in [0, \ldots, n]$, compute $a_i \in \Fb_q$ such
   that $a_i G = U_i - B_i$.
4. Output the polynomial $a(Z) = \sum_{i=0}^n a_i Z^i$.

Both commitment schemes are binding. It remains to specify the families
of functions $f_{\text{pp}}^{(1)}, f_{\text{pp}}^{(2)}$ that we use in the
respective zero-finding games. 

We define: $f_{\text{pp}}^{(1)}(p, h = [h_i]_{i=0}^n) := p - \sum_{i=0}^n \alpha^i h_i,$

and: $f_{\text{pp}}^{(2)}(p = [(h_i, U_i)]_{i=0}^n):$

1. Construct the key pair $(\text{ck}_0, \text{rk}_0) \leftarrow \PCDLTrim(\text{pp}_{\text{PC}}, \deg(h_i))$.
2. For each $i \in \{0, \ldots, n\}$, construct a $\PCDL$ commitment to $h_i$: $B_i \leftarrow \PCDLCommit(\text{ck}_0, h_i, \bot)$.
3. For each $i \in \{0, \ldots, n\}$, compute $a_i \in \mathbb{F}_q$ such that $a_i G = U_i - B_i$.
4. Output the polynomial $a(Z) := \sum_{i=0}^n a_i Z^i$.

---

We next describe an adversary $C$ against $\PCDL$, which simply
runs the soundness experiment for the accumulation scheme and outputs
$\text{acc}$ as output by $\mathcal{A}$. For convenience, we also have $C$
output $[q_i]_{i=1}^n$ and $\pi_V$; this will be ignored by the extractor.
**$C^\rho(\text{pp}_{\text{PC}})$:**

1. Set AS public parameters $\text{pp}_{\text{AS}} := 1^\lambda$.
2. Compute $(i_\phi, [q_i]_{i=1}^n, \text{acc}, \pi_V) \leftarrow
   \mathcal{A}^\rho(\text{pp}_{\text{AS}}, \text{pp}_{\text{PC}})$.
3. Parse $i_\phi$ as the degree bound $N$.
4. Output $(N, \text{acc} = ((C, d, z, v), \pi); [q_i]_{i=1}^n, \pi_V)$.

---

We use the extractor $\mathcal{E}_C$ corresponding to $C$
to construct adversaries $B_1, B_2$ for zero-finding games
against $(CM_1, \{f_{\text{pp}}^{(1)}\}_{\text{pp}})$, $(CM_2,
\{f_{\text{pp}}^{(2)}\}_{\text{pp}})$ respectively, with $L = D$ where $D =
\text{poly}(\lambda)$ is the maximum degree parameter as in the soundness
experiment for the accumulation scheme.

**$B_j^\rho(\text{pp})$:**

1. Compute $(N, \text{acc}, [q_i]_{i=1}^n, \pi_V) \leftarrow
   C^\rho(\text{pp})$.
2. Parse $[a_i]_{i=1}^n$ as $((C_i, d_i, z_i, v_i), \pi_i)$ and $\pi_V$
   as $(h_0, U_0, w)$.
3. Compute $p \leftarrow \mathcal{E}_C^\rho(\text{pp})$.
4. For each $i \in [n]$, obtain $h_i$ and $U_i$ from $\pi_i$.
5. Compute $\alpha := \rho_1([(h_i, U_i)]_{i=0}^n)$.
6. If $j = 1$, output $((n, N), (p, h := ([h_i]_{i=0}^n)))$. If $j = 2$,
   output $((n, N), ([(h_i, U_i)]_{i=0}^n))$.
---

We show that either $B_1$ or $B_2$ wins its respective zero-finding game
with probability at least $\delta / 2 - \text{negl}(\lambda)$.

Since $D$ accepts with probability $\delta$, and by the extraction property
of $\PCDL$, the following holds with probability at least $\delta -
\text{negl}(\lambda)$: $\mathcal{E}_C$ outputs a polynomial $p$ such that $C$
is a commitment to $p$ with randomness $w$ (and so $C$ is a deterministic
commitment to $p$), $p(z) = v$, and $\deg(p) \leq d$; and, moreover,
$(\text{acc}, \{q_i\}_{i=1}^n, \pi_V)$ satisfies the left-hand side of
Eq. (7). This latter point implies that, parsing $q_i$ as $(C_i, d_i, z_i,
v_i, \pi_i)$ and letting $(h_i, U_i) := \PCDLSuccinctCheck^\rho
(\text{rk}, C_i, d_i, z_i, v_i, \pi_i)$:

- Since $\mathcal{V}^\rho(\text{avk}, [q_i]_{i=1}^n, \text{acc}, \pi_V)$
  accepts, the following are true:
  1. For each $i \in [n]$, $\PCDLSuccinctCheck$ accepts.
  2. $U_0$ is a commitment to $h_0$.
  3. Parsing $\text{acc}$ as $(C, d, z, v), \pi$ and setting $\alpha :=
     \rho_1([(h_i, U_i)]_{i=0}^n)$, we have that $z = \rho_1(C, [h_i]_{i=0}^n)$,
     $C = \sum_{i=0}^n \alpha^i U_i$, and $v = \sum_{i=0}^n \alpha^i h_i(z)$.

For some $i \in [n]$, $\Phi_{PC}^\rho(\text{pp}_{PC}, i_\phi, q_i)
= \PCDLCheck^\rho(\text{rk}, (C_i, d_i, z_i, v_i), \pi_i)
= 0$. By construction (see Appendix A.2), this implies that either
$\PCDLSuccinctCheck$ rejects, or the group element $U_i$ is not
a commitment to $h_i$.

---

The above tells us that there exists some $i \in [n]$ such that $U_i$
is not a commitment to $h_i$. In other words, if we define $B_i :=
\PCDLCommit(\text{ck}, h_i)$, then there exists an $i \in [n]$
such that $U_i \neq B_i$. Letting $a_i \in \mathbb{F}_q$ be such that $a_i
G = U_i - B_i$, we deduce that the polynomial $a(Z) = \sum_{i=0}^n a_i Z^i$
is not identically zero.

There are then two cases:

1. $C \neq \sum_{i=0}^n \alpha^i B_i$. Then since $C$ is a commitment to
   $p$, $p(X) - h(X)$ is not identically zero, but $p(z) = h(z)$. Hence $B_1$
   wins the zero-finding game against $(CM_1, \{f_{pp}^{(1)}\}_{pp})$.

2. $C = \sum_{i=0}^n \alpha^i B_i$. Then since $C = \sum_{i=0}^n \alpha^i U_i$,
   $a(Z)$ is a zero of the polynomial $a(Z)$. Hence $B_2$ wins the zero-finding
   game against $(CM_2, \{f_{pp}^{(2)}\}_{pp})$.

Since at least one of these two cases occurs with probability at least
$\delta / 2 - \text{negl}(\lambda)$, the claim follows.
