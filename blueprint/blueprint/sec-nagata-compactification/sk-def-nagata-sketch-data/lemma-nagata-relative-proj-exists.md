+++
id = "lemma-nagata-relative-proj-exists"
kind = "lemma"
title = "Existence and affine compatibility of relative Proj"
order = 13
uses = ["def-nagata-affine-proj", "def-nagata-relative-proj", "lemma-nagata-proj-chart-ring-cocycle"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

The relative Proj construction in
[def-nagata-relative-proj] exists as a scheme, is independent up to a
unique isomorphism compatible with the chosen affine-chart
identifications, and restricts over every affine open $V\subseteq X$ to
$\operatorname{Proj}(\Gamma(V,\mathcal A))$. These restriction
isomorphisms commute with further restriction and with the structural maps.

## Proof

Choose the index set of all affine opens $V\subseteq X$. For each $V$ put
$P_V=\operatorname{Proj}(\Gamma(V,\mathcal A))$. If $W\subseteq V$ is a
principal affine open, quasi-coherence gives the coefficientwise graded
localization

$$
\Gamma(V,\mathcal A)[s^{-1}]\;\xrightarrow{\sim}\;
\Gamma(W,\mathcal A),
$$

and the affine Proj construction gives an isomorphism from $P_W$ onto the
inverse image of $W$ in $P_V$. To cover an arbitrary overlap $V\cap V'$,
index the gluing datum by triples $(V,V',W)$ with $W$ affine and
$W\subseteq V\cap V'$, together with a principal refinement inside $W$.
The associated isomorphism is the map on each standard chart induced by the
displayed localization. Every overlap is covered by such indices, and the
maps are isomorphisms because localization is transitive.

The identity and inverse axioms are the cases $V=V'$ and exchange of the two
affine indices. On a triple overlap all routes send a fraction
$x/s^m$ to its image in the localization at the product of the three
denominators; hence the cocycle axiom is exactly
[lemma-nagata-proj-chart-ring-cocycle]. The datum therefore satisfies
the scheme-gluing axioms, so the Mathlib
construction `AlgebraicGeometry.Scheme.GlueData.glued` produces a
scheme $P$ and a morphism $P\to X$ (the degree-zero maps agree on every
overlap). Its restriction to $V$ is the specified $P_V$ by the restriction
field of the same gluing construction. A second affine cover produces the
same overlap datum after passing to the common refinement by affine opens;
the uniqueness field of `Scheme.GlueData.glued` gives a unique
isomorphism over $X$ that
respects all the local identifications. (No uniqueness among arbitrary
automorphisms over $X$ is asserted.) The same argument on a third
refinement proves compatibility with further restrictions.
