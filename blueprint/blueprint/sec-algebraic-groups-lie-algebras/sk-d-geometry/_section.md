+++
id = "sk-d-geometry"
kind = "section"
title = "Affine geometry and matrix groups"
order = 2475
uses = ["sk-d-linear"]
lean = ["Matrix.GeneralLinearGroup.CoordinateRing", "Matrix.GeneralLinearGroup.scheme", "Matrix.GeneralLinearGroup.homMulEquiv", "Matrix.GeneralLinearGroup.zeroLocus", "Matrix.GeneralLinearGroup.subgroupScheme", "Matrix.GeneralLinearGroup.identityComponent", "Matrix.GeneralLinearGroup.center", "Matrix.GeneralLinearGroup.RationalHom"]
+++
*Definition (sketch).*

An affine variety over $k$ is the spectrum of a
finitely generated reduced commutative $k$-algebra; reduced means that
the algebra has no nonzero nilpotents. Closed subvarieties are given by
radical ideals, and regular maps by homomorphisms of coordinate algebras
in the opposite direction. The Zariski topology has polynomial zero
loci as its closed sets. A closure is the smallest closed set containing
a given subset. A space is connected if it has no decomposition into
two nonempty disjoint open sets, and irreducible if it is not the union
of two proper closed sets. A constructible set is a finite union of
intersections of open and closed sets. Dimension is the supremum of
lengths of strict chains of prime ideals in the coordinate algebra.

A matrix algebraic group is a reduced closed subgroup $G\subseteq\GL(V)$,
with regular multiplication and inversion; its homomorphisms are regular
group homomorphisms. We identify its $k$-points with their matrices when
writing products. The identity component $G^\circ$ is the connected
component of $1$. The center $Z(G)$ is the reduced closed subgroup of
$G$ consisting of the elements of $G$ commuting with all $g\in G(k)$
(not the centralizer of $G$ in $\GL(V)$).

Uses: [sk-d-linear]
