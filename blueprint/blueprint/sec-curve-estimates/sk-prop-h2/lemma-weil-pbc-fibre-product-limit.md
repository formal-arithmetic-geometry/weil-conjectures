+++
id = "lemma-weil-pbc-fibre-product-limit"
kind = "lemma"
title = "Base change commutes with the neighbourhood limit"
order = 945
uses = ["def-weil-pbc-scheme-conventions", "def-weil-pbc-strict-henselization-limit"]
+++
For a quasi-compact and quasi-separated $f:X\to S$,

$$
X\times_SS_{(\bar s)}\cong
\varprojlim_{(V,\bar v)}(X\times_SV).
$$

## Proof

On affine charts $X_0=\operatorname{Spec}B$ over
$S_0=\operatorname{Spec}A$, the left side has coordinate ring
$B\otimes_A\varinjlim A_V$. Tensor product commutes with filtered colimits,
so this is $\varinjlim(B\otimes_AA_V)$, the coordinate ring of the inverse
limit on the right. Quasi-compactness gives finitely many charts and
quasi-separatedness gives quasi-compact pairwise intersections; the affine
identifications therefore glue.

## Detailed form

If $f:X\to S$ is quasi-compact and quasi-separated
[def-weil-pbc-scheme-conventions], then

$$
 X\times_SS_{(\bar s)}\xrightarrow{\sim}
 \varprojlim_{(V,\bar v)}X\times_SV.
$$

## Proof

On affine charts, tensor products commute with filtered colimits, and
quasi-compactness gives finitely many charts while quasi-separatedness gives
quasi-compact pairwise intersections; the affine identifications glue to the
displayed identification of
[def-weil-pbc-strict-henselization-limit].
