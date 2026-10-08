+++
id = "cor-amb-affine-space-adjunction"
kind = "theorem"
title = "Affine-space ambient adjunction"
order = 1574
tags = ["latex:corollary"]
uses = ["def-amb-etale-compact-support", "def-coefficient-twists-detailed", "def-sbc-affine-space", "def-weil-pbc-derived-categories", "lem-amb-etale-adjoint-locality", "lem-amb-etale-compact-comparisons", "thm-amb-p1-adjunction"]
+++
For $p_d:\mathbf A^d_S\to S$, on the entire ordinary
derived categories of etale $A$-module sheaves,

$$
Rp_{d!}\dashv p_d^*(d)[2d].
$$

The notation refers to affine space, ordinary etale compact supports, and Tate twists.

## Proof

Let $j:\mathbf A^1_S\hookrightarrow\mathbf P^1_S$.
The definition in [def-amb-etale-compact-support]
is $Rp_{1!}=Rq_*j_!$. By
[thm-amb-p1-adjunction], [lem-amb-etale-adjoint-locality],
its right adjoint is $j^*q^*(1)[2]=p_1^*(1)[2]$.
For $d=0$ the assertion is the identity adjunction.
The composition of compact-support functors is
[lem-amb-etale-compact-comparisons]. For $d>0$, factor the affine-space projection into
$d$ successive affine-line projections. The right
adjoint of the composite is the reversed composite of
their right adjoints, by their Hom adjunction bijections.
The twists add by [def-coefficient-twists-detailed], giving
$p_d^*(d)[2d]$.
