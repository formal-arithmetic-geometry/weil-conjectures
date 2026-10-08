+++
id = "sk-p-product"
kind = "section"
title = "The central–geometric product"
order = 2522
uses = ["sk-d-geometry", "sk-d-monodromy", "sk-d-tangent", "sk-i-cartier", "sk-i-restriction", "sk-p-comparison", "sk-p-geometry", "sk-p-lie"]
lean = ["AlgebraicGeometry.GeneralLinearGroup.surjective_mulCenterIdentityComponent", "AlgebraicGeometry.GeneralLinearGroup.exists_mul_eq_of_containsCommutators", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.surjective_mul_center_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_mem_center_mul_mem_geometricMonodromy_eq"]
+++
*Proposition (sketch).*

For a semisimple represented degree datum, the
identity components and center satisfy

$$
G^\circ=Z(G^\circ)^\circ H^\circ.
$$

## Proof

Use the defining representation of [sk-d-monodromy].
By [sk-i-restriction], its restriction to the normal subgroup
$G^\circ$ is semisimple. By [sk-p-comparison], so is the action of
$\mathfrak g=\Lie(G^\circ)$, which is faithful because its differential
is the inclusion in $\End(V)$ from [sk-d-tangent].
Set $\mathfrak h=\Lie(H^\circ)$ and $T=Z(G^\circ)^\circ$.
Then [sk-p-lie], [sk-i-restriction], [sk-p-comparison] give

$$
\mathfrak g=Z(\mathfrak g)+[\mathfrak g,\mathfrak g]
=Z(\mathfrak g)+\mathfrak h
=\Lie(T)+\Lie(H^\circ).
$$

The multiplication map $T\times H^\circ\to G^\circ$ is a homomorphism,
so its image $K=TH^\circ$ is closed by [sk-p-geometry]. Its differential
is $(x,y)\mapsto x+y$, by [sk-i-cartier]; its image lies in $\Lie(K)$
and equals $\mathfrak g$. Thus [sk-i-cartier] gives
$\dim K=\dim G^\circ$, and [sk-p-geometry] gives $K=G^\circ$.

Uses: [sk-d-geometry], [sk-d-monodromy], [sk-d-tangent], [sk-i-cartier], [sk-i-restriction], [sk-p-comparison], [sk-p-geometry], [sk-p-lie]
