+++
id = "lemma-nagata-relative-affine-space-charts"
kind = "lemma"
title = "Relative affine-space charts and base change"
order = 309
uses = ["def-nagata-relative-affine-space"]
+++
**Status.** Bypassed by the formalized route: relative affine space is
`AlgebraicGeometry.AffineSpace`, which already carries its charts and
base change, so they are not reconstructed here.

The affine charts in [def-nagata-relative-affine-space] glue to a
scheme over $S$. Their transition maps satisfy the cocycle condition,
and for every $T\to S$ there is a canonical isomorphism
$\mathbb A^n_S\times_ST\cong\mathbb A^n_T$ compatible with the charts.

## Proof

On an affine $V=\operatorname{Spec}(R)$, localization gives
$R[T_1,\ldots,T_n]_a\cong R_a[T_1,\ldots,T_n]$. On a triple of principal
opens both composites send each polynomial coefficient to its image in the
localization at the product of the denominators, so the cocycle equality is
literal. Scheme gluing therefore produces the asserted scheme and map to
$S$. After base change to $T$, the same affine charts become
$\operatorname{Spec}(\Gamma(W,\mathcal O_T)[T_1,\ldots,T_n])$ on affine
$W\subseteq T$; the chartwise identifications agree on overlaps and hence
glue to the stated base-change isomorphism.
