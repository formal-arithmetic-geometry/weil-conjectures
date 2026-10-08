+++
id = "sk-d-real-operations"
kind = "section"
title = "Operations, constituents and coinvariants"
order = 2585
uses = ["sec-algebraic-groups-lie-algebras", "sec-six-functors", "sk-d-real-weil"]
lean = ["AlgebraicGeometry.WeilGroup.constLine", "AlgebraicGeometry.WeilGroup.tateLine", "Representation.IsIrreducible", "Representation.IsConstituent"]
+++
*Definition (sketch).*

For Weil representations use the ordinary direct sum,
diagonal tensor action, exterior action on $\bigwedge^r V$, dual action
$(g\lambda)(v)=\lambda(g^{-1}v)$, and determinant
$\det V=\bigwedge^{\dim V}V$. An irreducible representation is nonzero
with no proper nonzero invariant subspace. Constituents are irreducible
successive quotients of a composition series, counted with multiplicity;
their direct sum is a semisimplification.
For a subgroup $I$, set
$V^I=\{v:gv=v\text{ for all }g\in I\}$ and
$V_I=V/\langle gv-v:g\in I,v\in V\rangle$.
For $b\in\Qlb^\times$, the constant Weil line $B_b$ has action
$g\mapsto b^{\deg g}$. The Tate line is $\Qlb(n)=B_{q^{-n}}$.

Uses: [sk-d-real-weil]
