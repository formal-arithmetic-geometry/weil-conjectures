+++
id = "cor-pd-pic0-base-change"
kind = "theorem"
title = "The degree-zero part is compatible with base change"
order = 855
tags = ["latex:corollary"]
uses = ["def-pc-base-change", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-pd-degree-morphism", "lem-pd-degree-locally-constant", "lem-pd-picard-base-change"]
+++
Let $k$ be a field, let $C$ be a
smooth projective curve over $k$
which is geometrically integral,
and let $k'/k$ be a field extension. Then the
base change of the
degree-zero part along
$\Spec(k')\to\Spec(k)$ is the degree-zero part of the base change:

$$
\operatorname{Pic}^0_{C/k}\times_k k'\;\cong\;\operatorname{Pic}^0_{C_{k'}/k'} .
$$

## Proof

By [lem-pd-picard-base-change] the functor
$\operatorname{Pic}_{C/k}$ restricts to
$\operatorname{Pic}_{C_{k'}/k'}$ on the slice over $k'$, and the restriction of
a functor to a slice is the base change in the sense of
[def-pc-base-change]. The degree morphism of
[def-pd-degree-morphism] is defined through the fibrewise degree, and
[lem-pd-degree-locally-constant](3) says precisely that it is compatible
with this restriction: the restriction of
$\deg:\operatorname{Pic}_{C/k}\to\underline{\Z}$ is the degree morphism of
$C_{k'}$. Restricting the kernel of a morphism of sheaves to a slice gives
the kernel of the restricted morphism, so the two degree-zero parts agree after
base change, which is the displayed isomorphism.
