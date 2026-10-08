+++
id = "cor-fin-projective-curve-finite-group"
kind = "theorem"
title = "Finite constant groups on projective curve families"
order = 1617
tags = ["latex:corollary"]
uses = ["def-pc-projective-morphism", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "thm-constructible-serre", "thm-fin-projective-curve-constant"]
+++
Let $f:X\to S$ be a projective
morphism of finite-type
schemes over a field, with geometric fibre dimensions at most one.
If the order of a finite abelian group $M$ is invertible on $S$,
every higher direct image
$R^qf_*\underline M$ is
constructible.

## Proof

A finite abelian group has a finite filtration with successive
quotients $\mathbf F_\ell$, for primes $\ell$ dividing its order.
Taking constant sheaves is exact, as may be checked on every stalk.
Proceed by induction along this filtration, starting from
[thm-fin-projective-curve-constant].
For $0\to M'\to M\to M''\to0$, the long exact sequence identifies
$R^qf_*\underline M$ in a short exact sequence with left term

$$
\operatorname{coker}(R^{q-1}f_*\underline {M''}
\to R^qf_*\underline {M'})
\quad\hbox{and right term}\quad
\ker(R^qf_*\underline {M''}\to R^{q+1}f_*\underline {M'}).
$$

All four sheaves are constructible by induction, with the
negative-degree term zero. The kernel, cokernel and extension
clauses of [thm-constructible-serre] finish the induction.
