---
title: Investigating IVC with Halo2
author: 
  - Rasmus Kirk Jakobsen - 201907084
  - Abdul Haliq Abdul Latiff - 202303466
geometry: margin=2cm
header: |
  \usepackage[style=iso]{datetime2}
  \usepackage{amsmath,bm}
  \usepackage{emoji}
  \newcommand*\mod{\bmod}
  \newcommand*\cat{\mathbin{+\mkern-10mu+}}
  \newcommand*\bor{\mathbin{\&\mkern-7mu\&}}
  \newcommand*\xor{\oplus}
  \newcommand*\Bb{\mathbb{B}}
  \newcommand*\Zb{\mathbb{Z}}
  \newcommand*\Nb{\mathbb{N}}
  \newcommand*\Rb{\mathbb{R}}
  \newcommand*\Eb{\mathbb{E}}
  \newcommand*\Gb{\mathbb{G}}
  \newcommand*\Ac{\mathcal{A}}
  \newcommand*\Rc{\mathcal{R}}
  \newcommand*\Oc{\mathcal{O}}
  \newcommand*\Pc{\mathcal{P}}
  \newcommand*\Vc{\mathcal{V}}
  \newcommand*\Sc{\mathcal{S}}
  \newcommand*\Hc{\mathcal{H}}
  \newcommand*\a{\alpha}
  \newcommand*\b{\beta}
  \newcommand*\d{\delta}
  \newcommand*\e{\epsilon}
  \newcommand*\l{\lambda}
  \newcommand*\p{\phi}
  \newcommand*\ps{\psi}
  \newcommand*\S{\Sigma}
  \newcommand*\beq{\stackrel{?}{=}}
  \renewcommand*\PCDL{\text{PC}_{\text{DL}}}
  \renewcommand*\ASDL{\text{AS}_{\text{DL}}}
  \renewcommand*\plainspace{\mathcal{P}}
  \renewcommand*\cipherspace{\mathcal{C}}
  \renewcommand*\keyspace{\mathcal{K}}
  \newcommand*\meq{\stackrel{?}{=}}
  \newcommand{\qed}{\hfill \ensuremath{\Box}}
  \newcommand{\enddef}{\hfill \ensuremath{\triangle}}
  \newcommand{\floor}[1]{\left \lfloor #1 \right \rfloor }
  \newcommand{\ceil}[1]{\left \lceil #1 \right \rceil }
  \newcommand{\vec}[1]{ \boldsymbol{#1} }
  \newcommand{\ran}[1]{ \mathrm{#1} }
  \newcommand{\ranvec}[1]{ \boldsymbol{\ran{#1}} }
  \newcommand*\Gen{\textsc{Gen}}
  \newcommand*\Commit{\textsc{Commit}}
  \newcommand*\CheckParams{\textsc{CheckParams}}
---

Halo2, can be broken down into the following components:

- **Plonk**: A general-purpose zero-knowledge proof scheme.
- **$\PCDL$**: A Polynomial Commitment Scheme in the Discrete Log setting.
- **$\ASDL$**: An Accumulation Scheme in the Discrete Log setting.
- **Pasta**: A Cycle of Elliptic Curves, namely **Pa**llas and Ve**sta**.

This project is focused on the components of $\PCDL$ and $\ASDL$.


