+++
id = "pqf-lem-qs-intersection-qc"
kind = "lemma"
title = "Intersections of quasi-compact opens"
order = 194
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a
quasi-separated scheme and
let $U,V\subset X$ be quasi-compact open subschemes. Then
$U\cap V$ is a quasi-compact open subscheme.

## Proof

The affine opens form a basis of the topology of a scheme, so the
quasi-compact opens $U$ and $V$ are finite unions of affine opens,
$U=U_1\cup\dots\cup U_m$ and $V=V_1\cup\dots\cup V_n$. Then
$U\cap V=\bigcup_{i,j}(U_i\cap V_j)$ is a finite union, so it suffices
to treat the case that $U$ and $V$ are affine. In the product
$X\times X$ the rectangle $U\times V$ is affine, hence
quasi-compact, and the diagonal $\Delta:X\to X\times X$ is a
quasi-compact morphism, because $X$ is quasi-separated
([def-weil-pbc-scheme-conventions]). By the definition of a
quasi-compact morphism in [def-weil-pbc-scheme-conventions] the
preimage of the affine open $U\times V$ under $\Delta$ is
quasi-compact. The diagonal is the identity on points, so that preimage
is $U\cap V$.
