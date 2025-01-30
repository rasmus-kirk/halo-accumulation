---
title: Proving Type Preservation of $\beta$-reduction in System F
author:
  - Rasmus Kirk Jakobsen
theme: Berlin
#colortheme: rose
date: 2024-01-08
institute: Computer Science Aarhus
fontsize: 9pt
lang: en-US
section-titles: true
toc: true
header-includes: |
  \usepackage{amsmath,bm}
  \newcommand*\mod{\bmod}
  \newcommand*\bZ{\mathbb{Z}}
  \newcommand*\bB{\mathbb{B}}
  \newcommand*\a{\alpha}
  \newcommand*\b{\beta}
  \newcommand*\l{\lambda}
  \newcommand*\r{\rho}
  \newcommand*\s{\sigma}
  \newcommand*\t{\tau}
  \newcommand*\D{\Delta}
  \newcommand*\L{\Lambda}
  \newcommand*\G{\Gamma}
  \newcommand*\proves{\vdash}
  \newcommand*\to{\rightarrow}
  \newcommand*\={\equiv}
  \newcommand*\gt{>}
  \newcommand*\meq{\stackrel{?}{=}}
  \newcommand{\qed}{\hfill \blacksquare}
  \newcommand{\floor}[1]{\left \lfloor #1 \right \rfloor }
  \newcommand{\ceil}[1]{\left \lceil #1 \right \rceil }
  \newcommand{\vec}[1]{ \boldsymbol{#1} }
  \newcommand{\ran}[1]{ \mathrm{#1} }
  \newcommand{\ranvec}[1]{ \boldsymbol{\ran{#1}} }
---

# Overview & System F

## Introduction
- STLC
- $\beta$-reduction
- System F

## Overview Graph - Project

\begin{figure}
\begin{center}
\includegraphics[width=1\textwidth]{./figures/ov1.pdf}
\end{center}
\end{figure}

## Overview Graph - Theorems

\begin{figure}
\begin{center}
\includegraphics[width=0.47\textwidth]{./figures/ov2.pdf}
\end{center}
\end{figure}

## The Type System - Types {.fragile}

$$\t_1, \t_2 := X \quad | \quad \t_1 \to \t_2 \quad | \quad \forall \a. \t_1$$

\begin{lstlisting}[language=Coq]
(* Definitions of Types *)
Inductive type :=
| tvar : idType -> type
| tarr : type -> type -> type
(* Extension: System F *)
| tforall : idType -> type -> type.
\end{lstlisting}

## The Type System - Terms {.fragile}

$$
  \begin{matrix}
    t_1,t_2 := & x & | & \l x : \t. t_1 & | & t_1 \; t_2 \\
               &   & | & \D \a. t_1     & | & t_1 \; \t
  \end{matrix}
$$

\begin{lstlisting}[language=Coq]
Inductive term :=
| var  : idTerm -> term
| lam  : idTerm -> type -> term -> term
| app  : term -> term -> term
(* Extension: System F *)
| tlam : idType -> term -> term.
| tapp : term -> type -> term
\end{lstlisting}

## The Type System - Typing Judgements for STLC {.fragile}

$$
  \frac{x:\t \in \G}{\G \proves x:\t}\textsc{\scriptsize(Variable)} \quad
  \frac{\G, x : \t_1 \proves t : \t_2 \quad \D \proves \t_1}{\G \proves (\l x : \s. t) : \t_1 \to \t_2}\textsc{\scriptsize(Term Introduction)}
$$
$$
  \frac{\G \proves t_1 : \t_1 \to \t_2 \quad \G \proves t_2 : \t_2}{\G \proves t_1 \; t_2 : \t_2}\textsc{\scriptsize(Term Application)}
$$

\begin{lstlisting}[language=Coq]
Inductive typed : envTerm -> envType -> term -> type -> Prop :=
  | var_typed : $\forall$ ($\Gamma$:envTerm) ($\Delta$:envType) (x:idTerm) ($\tau$:type),
    $\Gamma$ x = Some $\tau$ -> 
    typed $\Gamma$ $\Delta$ (var x) $\tau$
  | lam_typed : $\forall$ ($\Gamma$:envTerm) ($\Delta$:envType) (x:idTerm) (t : term) ($\tau_1$ $\tau_2$ : type),
    delta $\Delta$ $\tau_1$ ->
    typed (overrideTerm $\Gamma$ x $\tau_1$) $\Delta$ t $\tau_2$ -> typed $\Gamma$ $\Delta$ (lam x $\tau_1$ t) (tarr $\tau_1$ $\tau_2$)
  | app_typed : $\forall$ ($\Gamma$:envTerm) ($\Delta$:envType) (t1 t2 : term) ($\tau_1$ $\tau_2$ : type),
    typed $\Gamma$ $\Delta$ $t_1$ (tarr $\tau_1$ $\tau_2$) -> 
    typed $\Gamma$ $\Delta$ $t_2$ $\tau_1$ -> 
    typed $\Gamma$ $\Delta$ (app $t_1$ $t_2$) $\tau_2$
  ...
\end{lstlisting}

## The Type System - Typing Judgements for System F {.fragile}

$$
  \frac{\D, \a; \G \proves t : \t}{\D; \G \proves \L \a. t : \forall \a. \t}\textsc{\scriptsize(Type Introduction)} \qquad
  \frac{\D; \G \proves t : \forall \a. \t_1 \quad \D \proves \t_2}{\D; \G \proves t \; \t_2 : \t_1[\a := \t_2]}\textsc{\scriptsize(Type Application)}
$$

\begin{lstlisting}[language=Coq]
  ...
  (* Extension: System F *)
  | tlam_typed : forall ($\Gamma$:envTerm) ($\Delta$:envType) ($\alpha$:idType) (t:term) ($\tau_2$:type),
    typed $\Gamma$ (overrideType $\Delta$ $\alpha$) t $\tau_2$ -> 
    typed $\Gamma$ $\Delta$ (tlam $\alpha$ t) (tforall $\alpha$ $\tau_2$).
  | tapp_typed : forall ($\Gamma$:envTerm) ($\Delta$:envType) ($\alpha$:idType) (t:term) ($\tau_1$ $\tau_2$ : type),
    delta $\Delta$ $\tau_1$ -> 
    typed $\Gamma$ $\Delta$ t (tforall $\alpha$ $\tau_2$) ->
    typed $\Gamma$ $\Delta$ (tapp t $\tau_1$) (substitutionTypeType $\tau_2$ $\alpha$ $\tau_1$)
\end{lstlisting}

# Problems encountered

## Term Substitution {.fragile}

$$
  \frac{\G \proves t_1 : \t_1 \quad \G,x:\t_1 \proves t_1 : \t_2}{\G \proves t_1[x:=t_2] : \t_2}\text{\scriptsize(\textsc{Substitution\textbf{!}})}
$$

\begin{lstlisting}[language=Coq]
Inductive term :=
| var  : id -> term
| app  : term -> term -> term
| lam  : id -> type -> term -> term
(* Substitution for beta-reduction: t1[x:=t2] *)
| sub : term -> id -> term -> term.
\end{lstlisting}

## Substitution

- **Substitution of Terms**: Substitutes a term variable for another term
  in a term.  
  For example: $(\l x : \t. x)[x := t] = (\l t : \t. t)$.
- **Substitution of Types in Types**: Substitutes a type variable for another
  type in a type.  
  For example: $\forall \a.(\a \to \t_2)[\a := \t_1] = (\t_1 \to \t_2)$.
- **Substitution of Types in Terms**: Substitutes a type variable for another
  type in a term.  
  For example: $\forall \a.(\l x : \a. x)[\a := \t] = (\l x : \t. x)$.

## Free Variables

- The notion of free variables in the given notes:
$$
  \frac{\G \proves M : \t \quad \a \not\in FV(\G)}{\G \proves \L \a. M : \forall \a. \t}\text{\scriptsize(\textsc{Type Introduction\textbf{!}})}
$$
- $\a \not \in FV(\G)$: $\a$ is not a free variable in the environment $\G$
- Split the environments!
- Still need notions of free variables...
- Dan Grossman:
$$
  \D \proves \t \quad \text{(All free variables in $\t$ are in $\D$)}
$$
- Implement custom environments and $\cre{delta}$

## Environments and Free Environments (Delta) {.fragile}

$$
  \frac{\a \in \D}{\D \proves \a}\text{\scriptsize(\textsc{Delta variable})} \qquad
  \frac{\D \proves \t_1 \quad \D \proves \t_2}{\D \proves \t_1 \to \t_2}\text{\scriptsize(\textsc{Delta $\to$})} \qquad
  \frac{\D, \a \proves \t}{\D \proves \forall \a . \t}\text{\scriptsize(\textsc{Delta $\forall$})} \qquad
$$

\begin{lstlisting}[language=Coq]
Inductive delta : envType -> type -> Prop :=
  | tvar_delta : $\forall$ ($\Delta$:envType) ($\alpha$:idType),
    $\Delta$ $\alpha$ = true ->
    delta $\Delta$ (tvar $\alpha$)
  | tarr_delta : $\forall$ ($\Delta$:envType) ($\tau_1$ $\tau_2$ : type),
    delta $\Delta$ $\tau_1$ ->
    delta $\Delta$ $\tau_2$ ->
    delta $\Delta$ (tarr $\tau_1$ $\tau_2$)
  | tforall_delta : $\forall$ ($\Delta$:envType) ($\alpha$:idType) ($\tau$: type),
    delta (overrideType $\Delta$ $\alpha$) $\tau$ ->
    delta $\Delta$ (tforall $\alpha$ $\tau$).
\end{lstlisting}

## Substitution preserves type preservation {.fragile}

- Starts out well!
\begin{lstlisting}[language=Coq]
(* Lemma: Type substitution preserves typing *)
Lemma type_substitution_preserves_typing : $\forall$ E D t T x Z,
  delta D Z ->
  typed E (overrideType D x) t T ->
  typed (substEnvTerm E x Z) D (substitutionTypeTerm t x Z) (substitutionTypeType T x Z).
Proof.
  intros E D t T x Z H1 H2.
  remember (overrideType D x) as D'.
  induction H2; subst; simpl.
  - apply var_typed. unfold substEnvTerm. rewrite H. reflexivity.
  - eapply app_typed.
    + apply IHtyped1. reflexivity.
    + apply IHtyped2. reflexivity.
  - apply lam_typed.
    ...
\end{lstlisting}

## Substitution preserves type preservation {.fragile}

- Then, not so much...
\begin{lstlisting}[language=Coq]
  ...
  - apply lam_typed.
    + admit.
    + admit.
  - admit.
  - destructEQ (beq_id_type x a).
    + apply tlam_typed. rewrite overrideType_shadow in H2.
      admit.
    + admit.
Admitted.
\end{lstlisting}

- What happens?
  - Unformalizable in Coq?
  - Unprovable theorem?
  - User error?
    - Don't know _how_ to prove it?
    - Wrong definitions?
- Let's look at the first $\cdkre{admit}$

## First case of `lam_typed` - Part 1 {.fragile}

\begin{lstlisting}[language=CoqGoal]
$\cb{D}$: $\cg{envType}$
$\cb{x}$: $\cg{idType}$
$\cb{Z}$: $\cg{type}$
$\cb{E}$: $\cg{envTerm}$
$\cb{x0}$: $\cg{idTerm}$
$\cb{t}$: $\cg{term}$
$\cb{A, B}$: $\cg{type}$
$\cb{IHtyped}$: $\cg{overrideType D x}$ $\co{=}$ $\cg{overrideType D x}$ $\color{ltorange} \rightarrow$
          $\cg{typed (substEnvTerm (overrideTerm E x0 A) x Z) D (substitutionTypeTerm t x Z)}$
            $\cg{(substitutionTypeType B x Z)}$
$\cb{H}$: $\cg{delta (overrideType D x) A}$
$\cb{H1}$: $\cg{delta D Z}$
$\cb{H2}$: $\cg{typed (overrideTerm E x0 A) (overrideType D x) t B}$
--------------------------------------------------------------
$\cre{Goal:}$
delta D (substitutionTypeType A x Z)
\end{lstlisting}

## First case of `lam_typed` - Part 2 {.fragile}

\begin{lstlisting}[language=Coq]
Lemma helper_lemma : $\forall$ $\Delta$ $\tau_1$ $\tau_2$ X,
  delta $\Delta$ $\tau_2$ ->
  delta (overrideType $\Delta$ X) $\tau_1$ ->
  delta $\Delta$ (substitutionTypeType $\tau_1$ X $\tau_2$).
Proof.
  intros $\Delta$ $\tau_1$ $\tau_2$ X H1 H2.
  ...
\end{lstlisting}

\begin{lstlisting}[language=CoqGoal]
$\color{ltblue}\Delta$: $\cg{envType}$
$\color{ltblue} \tau_1, \tau_2$: $\cg{type}$
$\cb{X}$: $\cg{idType}$
$\cb{H1}$: $\color{ltgreen} \cg{delta } \Delta \text{ } \tau_2$
$\cb{H2}$: $\color{ltgreen} \cg{delta (overrideType } \Delta \cg{ X) } \tau_1$
--------------------------------------------------------------
$\cre{Goal:}$
delta $\Delta$ (substitutionTypeType $\tau_1$ X $\tau_2$)
\end{lstlisting}

## Trying to prove $\D \proves \t_1[X := \t_2]$ {.fragile}

\begin{block}{Our hypotheses and goal:}
$$
\begin{aligned}
  \cre{Goal} &:= \D \proves \t_1[X := \t_2] \\
  \cb{H1} &:= \D \proves \t_2 \\
  \cb{H2} &:= \D,X \proves \t_1 \\
\end{aligned}
$$
\end{block}

- $\t_1[X:=\t_2]$ will contain no $X$'s
- All other types, except $X$, in $\t_1$ must be in $\D$ ($\cb{H2}$)
- All $X$'s have been replaced by $\t_2$
- All types in $\t_2$ are in $\D$ ($\cb{H1}$)

Thus, $\D \proves \t_2 \implies \D,X \proves \t_1 \implies \D \proves \t_1[X:=\t_2]$
$\qed$

# Conclusion

## Conclusion

### The project:
  - Main lemma _should_ be provable in Coq
  - \sout{Our definitions are probably wrong}
  - Our definitions _might_ be wrong
  - Proud despite unfinished state

### Coq:
  - Learned a lot about logic and proofs
  - The feedback loop
  - Formal vs informal
