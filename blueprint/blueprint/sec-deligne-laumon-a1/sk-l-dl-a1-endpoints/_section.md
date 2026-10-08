+++
id = "sk-l-dl-a1-endpoints"
kind = "section"
title = "Degree zero and degree two"
order = 2729
uses = ["sk-d-dl-a1-setup", "sk-p-linear-filtration", "sk-thm-derived-duality", "sk-thm-sf-dual-perfect", "sk-thm-sf-global-duality"]
lean = ["AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage", "AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero", "AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two", "AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two"]
+++
*Lemma (sketch).*

Let $j:U_0\hookrightarrow C_0$ be dense, with $C_0$ a smooth
geometrically connected affine curve, and let $F$ be lisse.
If $V$ is its generic geometric representation, then

$$
H_c^0(C,j_*F)=0,\qquad
H_c^2(C,j_*F)\simeq V_{\pi_1(U)}(-1).
$$

There is no cohomology outside degrees $0,1,2$. If $F$ is pure of
weight $w$, the degree-two group is pure of weight $w+2$ (possibly zero).

## Proof

A nonzero global section of a lisse sheaf has nonzero germs throughout
the connected open $U$. Its extension to $C$ therefore has support all
of the nonproper affine curve, so cannot be compactly supported.
The boundary has finite support and no positive cohomology; localization
identifies $H_c^2(C,j_*F)$ with $H_c^2(U,F)$. Global Verdier duality,
with $\mathbb D_UF=F^\vee(1)[2]$, applies to the smooth nonproper curve
$U$. Its degreewise form in [sk-thm-derived-duality] identifies the
latter group with $H^0(U,F^\vee)^\vee(-1)=V_{\pi_1(U)}(-1)$.
The coinvariants are the maximal geometrically constant quotient of $F$.
When $F$ is pure of weight $w$, at a closed point of degree $d$ the
coinvariants' Frobenius is the $d$th power of
the constant quotient's Frobenius, so purity of the stalk quotient gives
weight $w$ for that module. The twist adds two. Curve cohomological
dimension gives the remaining vanishings.

Uses: [sk-d-dl-a1-setup], [sk-thm-derived-duality], [sk-thm-sf-dual-perfect], [sk-thm-sf-global-duality]
