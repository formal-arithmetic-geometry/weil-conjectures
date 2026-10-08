+++
id = "lemma-weil-pbc-finite-stage-killing"
kind = "lemma"
title = "Finite-stage killing of a class"
order = 1125
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-etale-cohomology-continuity"]
+++
In an affine henselian pair, if a positive-degree class $c$ dies on an
integral strictly-local cover $T_\infty\to T_0$ represented by a filtered
system $\{T_\lambda\}$ of finite finitely presented covers, then there exists
$\lambda_0$ such that the pullback of $c$ to $H^q(T_{\lambda_0},F|)$ is zero.

## Proof

Represent the chosen cochain and its null-homotopy on the limit by finitely
many sections. Each section and each equality occurs at some index because
the system is filtered and the etale site is quasi-compact and quasi-separated.
Choose one index dominating those finitely many indices. The descended
cochain and the descended null-homotopy satisfy the coboundary equation at a
further finite index; replacing by that index gives $\lambda_0$. This exposes the indexing and
vanishing witness requested by Tag `09ZD`.

## Detailed form

Let $(T,T_0)$ be an affine henselian pair, let $F$ be torsion, and let $c\in
H^q(T_0,F|_{T_0})$ with $q>0$. Suppose $c$ vanishes after pullback to an
integral strictly local cover that is the inverse limit of finite, finitely
presented covers $T_\lambda\to T$. Then $c$ already vanishes after pullback to
one $T_{\lambda_0}$.

## Proof

The $T_\lambda\to T$ are finite, hence affine, so $(T_\lambda)$ is a
cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps (finite morphisms being affine); base changing along the
closed immersion $T_0\hookrightarrow T$ of the affine henselian pair, the
system $((T_\lambda)_0)$ is of the same kind, with limit $X_0=X\times_TT_0$,
and the pullbacks of the torsion sheaf $F_0$ form a compatible system. By the
continuity of etale cohomology along such limits,

$$
 \varinjlim_\lambda H^q((T_\lambda)_0,F_0|)
 \xrightarrow{\sim}H^q(X_0,F_0|),
$$

and the hypothesis that $c$ vanishes after pullback to the integral strictly
local cover $X$ says exactly that the element $(c|_{(T_\lambda)_0})$ maps to
zero in this colimit; an element of a filtered colimit that maps to zero is
already zero, so $c|_{(T_{\lambda_0})_0}=0$ for some $T_{\lambda_0}$, as
asserted.
