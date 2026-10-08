+++
id = "sk-p-geometry"
kind = "section"
title = "Algebraic-group geometry"
order = 2493
uses = ["sk-d-geometry", "sk-i-cartier", "sk-i-geometry"]
lean = ["Matrix.GeneralLinearGroup.isPrime_identityComponent", "Matrix.GeneralLinearGroup.normal_zeroLocus_identityComponent", "Matrix.GeneralLinearGroup.finiteIndex_zeroLocus_identityComponent", "Matrix.GeneralLinearGroup.toPrimeSpectrum_mem_connectedComponentIn_iff", "AlgebraicGeometry.isClosed_range_of_isMonHom", "AlgebraicGeometry.isIso_left_of_topologicalKrullDim_eq", "Matrix.GeneralLinearGroup.eq_of_ringKrullDim_eq"]
+++
*Proposition (sketch).*

For matrix algebraic groups over $k$:

0pt
0pt
1. $G^\circ$ is a closed, normal, irreducible subgroup, and its
finitely many cosets are exactly the connected components of $G$.
1. The image on $k$-points of a regular homomorphism $G\to K$
is a closed subgroup of $K$, with its reduced structure.
1. If $G$ is connected and a closed subgroup $J\subseteq G$ has
$\dim J=\dim G$, then $J=G$.

## Proof

By [sk-i-geometry], [sk-i-cartier], there are finitely many disjoint
irreducible components, each open and closed. Hence they are the
connected components of [sk-d-geometry]. Multiplication and inversion
preserve the identity component, and translations identify the others
with its cosets. Conjugation fixes $1$, so preserves $G^\circ$.
For a homomorphism, let $S$ be its image and $K'$ its closure. Continuity
of the group operations makes $K'$ a group. By [sk-i-geometry], $S$
is constructible and contains an open subset $U\ne\varnothing$ of $K'$.
Translating $U$ shows that $S$ is open; its other cosets are open too.
Thus $S$ is closed, and density gives $S=K'$. Finally, for connected
$G$, irreducibility and strict dimension drop in [sk-i-geometry]
exclude a proper closed subgroup of equal dimension.

Uses: [sk-d-geometry], [sk-i-cartier], [sk-i-geometry]
