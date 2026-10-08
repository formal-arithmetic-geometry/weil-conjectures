+++
id = "sk-i-restriction"
kind = "section"
title = "Normal restriction and passage to closure"
order = 2513
uses = ["sk-d-geometry", "sk-d-linear", "sk-d-monodromy", "sk-d-tangent", "sk-i-cartier", "sk-i-geometry"]
lean = ["Representation.isSemisimpleRepresentation_comp_subtype", "AlgebraicGeometry.IsMonHom.ContainsCommutators", "AlgebraicGeometry.IsMonHom.Normal.of_containsCommutators", "AlgebraicGeometry.GeneralLinearGroup.containsCommutators_subgroupSchemeHom", "AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap", "AlgebraicGeometry.GeneralLinearGroup.lie_mem_range_lieAlgebraMap_identityComponent", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.arithmeticMonodromy_le_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.normal_zeroLocus_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.commutator_zeroLocus_le_zeroLocus_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.containsCommutators_subgroupSchemeHom_arithmeticMonodromy_le_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.lie_mem_lieAlgebra_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.lie_mem_lieAlgebra_identityComponent_geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.isSemisimpleRepresentation_standardRepresentation_identityComponent", "AlgebraicGeometry.GeneralLinearGroup.derivedIdeal", "AlgebraicGeometry.GeneralLinearGroup.containsCommutators_iff_le_derivedIdeal", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.geometricMonodromy_le_derivedIdeal_arithmeticMonodromy"]
+++
*Proposition (sketch).*

A finite-dimensional semisimple representation restricts semisimply
to a normal subgroup (the finite-dimensional normal-restriction argument).
For a rational action, invariance under a Zariski-dense subgroup is
equivalent to invariance under its closure: the stabilizer equations
are closed. Invariant subspaces and quotients carry induced rational
actions; direct sums, tensor products, exterior powers and determinants
of rational actions are rational. The closures $G,H$ of
[sk-d-monodromy] are algebraic groups, $H$ is normal in $G$, and

$$
aba^{-1}b^{-1}\in H\quad(a,b\in G),\qquad
[\Lie(G^\circ),\Lie(G^\circ)]\subseteq\Lie(H^\circ).
$$

These are the statements about [sk-d-linear], [sk-d-geometry],
[sk-d-tangent] used in the monodromy arguments below.
lem:clifford-restriction;lem:monodromy-stable;lem:monodromy-normal;lem:monodromy-commutators;lem:monodromy-lie-commutators;lem:rational-subquotients;lem:rational-direct-sum;lem:rational-tensor;lem:rational-exterior;lem:rational-determinant

## Proof

*Normal restriction.* It is enough to treat a simple representation
$V$ of a group $\Gamma$ and a normal subgroup $N$. Choose an
$N$-invariant $U\ne0$ of least positive dimension; minimality makes $U$
simple for $N$. For $g\in\Gamma$, $n\in N$ and $u\in U$, normality gives
$n(gu)=g(g^{-1}ng)u\in gU$, and an $N$-invariant $S\subseteq gU$ has
$g^{-1}S\subseteq U$ invariant, so $S=0$ or $S=gU$; every translate $gU$
is therefore simple for $N$. The sum of the translates is nonzero and
$\Gamma$-invariant, hence all of $V$. Starting from $U$, a proper direct
sum $D$ of translates misses some $gU$, and $gU\cap D$ is a proper
$N$-subspace of a simple module, hence zero, so $gU$ may be adjoined.
The dimension strictly increases, so after at most $\dim V$ steps $V$ is a
direct sum of simple $N$-modules. Neither finiteness of $\Gamma$ nor
finite index of $N$ is used.

*Density and stabilizers.* In a basis adapted to a subspace, the
stabilizer is cut out by the vanishing of one matrix block, so it is
closed and its points are exactly the elements preserving the subspace.
Containing a Zariski-dense subgroup, it contains the closure; the reverse
implication is restriction. The closures are algebraic groups: for
$a\in\Gamma$ left translation preserves $\Gamma$, so $aK=K$; for fixed
$y\in K$ the condition $xy\in K$ is closed and contains $\Gamma$, hence
$K$, giving $KK\subseteq K$; inversion is the same argument. Since
$K\times K$ is reduced by [sk-i-geometry], the vanishing principle there
turns these pointwise inclusions into regular group operations, and the
group identities are inherited from matrices.

*Rationality of the operations.* For a subquotient $A/B$ with
$B\subseteq A$ invariant under a dense subgroup, both are invariant under
the closure by the previous paragraph. In a basis adapted to
$B\subseteq A\subseteq M$ the matrix of $r(g)$ is block upper triangular;
the diagonal block at $A/B$ has regular entries, as does the corresponding
block of $r(g^{-1})$, so the induced action is a regular map to the
general linear group of the subquotient. A direct sum is block diagonal in
the original entries. In the tensor basis the entries are the products
$a_{ij}b_{uv}$; in the exterior basis they are the corresponding minors,
polynomials in the original entries, and the inverse is given by the same
formulas at $g^{-1}$. The determinant is the top exterior power on a
one-dimensional space, hence a rational character.

*Normality and commutators.* The kernel $P$ of the degree map in
[sk-d-monodromy] is normal, so conjugation by an element of $\rho(W)$
preserves $\rho(P)$ and, being a homeomorphism, preserves its closure $H$.
For fixed $h\in H$ the condition $ghg^{-1}\in H$ is closed in $G$ and
contains $\rho(W)$, hence contains $G$; applying it to $g^{-1}$ gives
$gHg^{-1}=H$. Since $\mathbf Z$ is abelian the degree map kills
commutators, so commutators of elements of $\rho(W)$ lie in $H$. Fixing
one variable, $a\mapsto aba^{-1}b^{-1}$ is regular, so the preimage of $H$
is closed and contains $\rho(W)$, hence $G$; fixing $a\in G$ and repeating
in the other variable gives the assertion on all of $G\times G$. No
quotient algebraic group is needed.

*The Lie inclusion.* The commutator morphism $G\times G\to G$ sends
every $k$-point into $H$, and its source is reduced by [sk-i-geometry],
so the vanishing principle there factors it through $H$ — which must be
done before evaluating on nonreduced rings. For
$X,Y\in\Lie(G^\circ)$ take
$R=k[\varepsilon,\delta]/(\varepsilon^2,\delta^2)$; direct matrix
multiplication gives

$$
(1+\varepsilon X)(1+\delta Y)(1-\varepsilon X)(1-\delta Y)
=1+\varepsilon\delta(XY-YX),
$$

an $R$-point of $H$. For a defining equation $f$ of $H$, expansion at $1$
reads $f(1+\varepsilon\delta Z)=f(1)+\varepsilon\delta\,df_1(Z)$, and
$\varepsilon\delta$ is linearly independent of $1,\varepsilon,\delta$ in
$R$, so $df_1([X,Y])=0$. The linear tangent equations of [sk-d-tangent]
put $[X,Y]$ in $\Lie(H)$, which equals $\Lie(H^\circ)$ by
[sk-i-cartier]. Spanning over all such brackets gives the inclusion.

Uses: [sk-d-geometry], [sk-d-linear], [sk-d-monodromy], [sk-d-tangent], [sk-i-cartier], [sk-i-geometry]
