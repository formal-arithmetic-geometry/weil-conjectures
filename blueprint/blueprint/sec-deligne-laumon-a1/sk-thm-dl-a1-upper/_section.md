+++
id = "sk-thm-dl-a1-upper"
kind = "section"
title = "Deligne–Laumon affine-line estimate"
order = 2785
uses = ["sk-c-dl-a1-hc1", "sk-d-dl-a1-setup", "sk-l-dl-a1-endpoints", "sk-p-dl-a1-exact", "sk-p-linear-filtration"]
lean = ["AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMost_compactlySupportedCohomology_directImage", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_directImage_zero", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isPureOfWeightOver_compactlySupportedCohomology_directImage_two"]
+++
*Theorem (sketch).*

Let $j:U_0\hookrightarrow A_0$ be a dense open immersion and let $F$
be a lisse Weil sheaf, punctually $\iota$-pure of weight $w$ and
unramified at infinity. For every integer $r$,

$$
H_c^r(A,j_*F)\quad\text{has weights at most }w+r.
$$

More precisely, degree zero vanishes, degree two is pure of weight
$w+2$, and only the degree-one upper bound requires the Fourier argument.

## Proof

The endpoint lemma settles all degrees except one. Choose a finite
composition filtration of the Weil representation of $F$; finite
dimension ensures termination. Its lisse irreducible factors remain
pure of weight $w$, since their stalk spectra are subquotient spectra,
and remain unramified at infinity.

A geometrically constant factor extends constantly to $A_0$ and has
$H_c^1=0$, since $R\Gamma_c(A,\DLAQ)=\DLAQ(-1)[-2]$.
Every other factor satisfies [sk-c-dl-a1-hc1]. By
[sk-p-dl-a1-exact], each filtration step remains a short exact
sequence after applying $j_*$. The compact-support long exact sequence
then gives an exact triple in degree one. Its middle term inherits
the common upper bound from its two outer terms, because characteristic
polynomials multiply in short exact sequences of Frobenius modules.
Induction through the filtration proves the result. No splitting of
the filtration or semisimplicity theorem for pure sheaves is required.

Uses: [sk-c-dl-a1-hc1], [sk-d-dl-a1-setup], [sk-l-dl-a1-endpoints], [sk-p-dl-a1-exact]
