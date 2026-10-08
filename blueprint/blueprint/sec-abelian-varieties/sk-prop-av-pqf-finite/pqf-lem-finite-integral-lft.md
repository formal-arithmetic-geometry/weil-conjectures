+++
id = "pqf-lem-finite-integral-lft"
kind = "lemma"
title = "Finite morphisms are integral"
order = 496
uses = ["def-weil-pbc-scheme-conventions"]
+++
A finite morphism of
schemes is integral.
(*Stacks Project, Morphisms of Schemes, Lemma 29.45.4, Tag
[01WJ](https://stacks.math.columbia.edu/tag/01WJ).*)

## Proof

We work ring-locally. Recall the classical determinant trick:
if $A\to B$ is a finite ring homomorphism, i.e. $B$ is a finite
$A$-module, then every $b\in B$ is integral over $A$: choosing
$b_1,\dots,b_n$ generating $B$ as an $A$-module and writing
$b\,b_j=\sum_i c_{ij}\,b_i$ with $c_{ij}\in A$, the vector
$(b_1,\dots,b_n)$ is annihilated by the matrix $b\cdot\mathrm{id}-C$,
$C=(c_{ij})$, so the adjugate argument gives a monic equation
$b^n+a_{n-1}b^{n-1}+\dots+a_0=0$ with $a_k\in A$ (the characteristic
polynomial of the multiplication map $b\cdot$).
Now let $f:X\to S$ be finite: $f$ is affine and $f_*\mathcal O_X$ is
a finite $\mathcal O_S$-algebra, by
[def-weil-pbc-scheme-conventions]; for $V=\operatorname{Spec}A$
affine open in $S$ and $f^{-1}(V)=\operatorname{Spec}B$ the ring map
$A\to B$ is finite, so every element of $B$ is integral over $A$ by
the determinant trick, which is exactly the assertion that
$f_*\mathcal O_X$ is integral over $\mathcal O_S$; with affineness
this is $f$ integral.
