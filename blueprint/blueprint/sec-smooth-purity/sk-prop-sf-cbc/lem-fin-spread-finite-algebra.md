+++
id = "lem-fin-spread-finite-algebra"
kind = "lemma"
title = "Spreading a finite algebra from the generic fibre"
order = 1612
uses = ["def-weil-pbc-scheme-conventions", "lem-pc-section-clearing-denominators", "pqf-def-coherent"]
+++
Let $A$ be a Noetherian domain with fraction field $K$, and let
$T\to\operatorname{Spec}A$ be
projective.
Every finite coherent
$\mathcal O_{T_K}$-algebra extends to a finite
$\mathcal O_{T_{A[a^{-1}]}}$-algebra for some $0\ne a\in A$.
A finite product decomposition of the generic algebra can be extended
at the same time.

## Proof

Choose a finite affine cover $T_i=\operatorname{Spec}B_i$.
The rings are Noetherian. On $T_{i,K}$ the algebra is a finitely
presented $B_i\otimes_AK$-module. Choose generators, a finite
matrix of module relations, products of each pair of generators,
and a unit. They use finitely many fractions from $A$.
Clear their denominators. The claims that the product respects
the relations, is associative, commutative and unital are finitely
many equalities in finitely presented modules. An equality holding
after localization at $A\setminus\{0\}$ holds after inverting one
nonzero element of $A$. Invert the product of these elements.

The intersections $T_i\cap T_j$ are quasi-compact, and admit finite
covers by distinguished affine opens of each $T_i$. Descend the
generic gluing isomorphisms, their inverses, and the cocycle
equalities on finite affine covers of triple intersections in the
same way: maps from a finitely presented module are specified by
finitely many generator images and relations. Clearing the
finitely many additional denominators makes the gluings valid.
This is the module-localization calculation underlying
[pqf-def-coherent] and the finite-cover clearing argument
[lem-pc-section-clearing-denominators]; no direct-image
constructibility is used. The glued algebra is finite on every
$T_i$. To extend a product decomposition, descend each factor
and its multiplication separately, then take their finite product.
