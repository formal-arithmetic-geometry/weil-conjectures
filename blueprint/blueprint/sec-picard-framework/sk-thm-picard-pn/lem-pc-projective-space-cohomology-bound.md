+++
id = "lem-pc-projective-space-cohomology-bound"
kind = "lemma"
title = "Cohomology above the number of projective coordinates"
order = 621
uses = ["def-pc-projective-space-twist", "lem-pc-cech-computes", "pqf-def-coherent", "pqf-def-cohomology"]
+++
For any commutative ring $A$, any $n\ge0$, and any
quasi-coherent module $\mathcal F$ on
$\hyperref[def-pc-projective-space-twist]{\mathbf P^n_A}$,
one has $H^q(\mathbf P^n_A,\mathcal F)=0$ for $q>n$.

## Proof

The $n+1$ standard opens of [def-pc-projective-space-twist]
have affine intersections, so [lem-pc-cech-computes] applies.
The alternating Cech complex has no terms in degrees greater than
$n$, because no subset of the $n+1$ indices has more than $n+1$
elements. Its cohomology in those degrees is zero.
