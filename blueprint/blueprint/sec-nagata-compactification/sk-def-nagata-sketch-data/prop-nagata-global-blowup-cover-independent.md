+++
id = "prop-nagata-global-blowup-cover-independent"
kind = "theorem"
title = "The global blow-up map, its affine restrictions, and independence of the affine cover"
order = 56
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowup", "AlgebraicGeometry.Scheme.IdealSheafData.blowupMap", "AlgebraicGeometry.Scheme.IdealSheafData.blowupMap_preimage", "AlgebraicGeometry.Scheme.IdealSheafData.blowupι_blowupMap", "AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupι"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-global-blowup-overlap-cocycle", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-restrict", "prop-nagata-rees-graded"]
+++
The constructed comparison is the unique isomorphism over $X$ restricting
to the identity comparison on every common affine refinement.

## Proof

By [prop-nagata-global-blowup-cover-independent], the comparison is an
isomorphism on every member of the common refinement. The overlap cocycle
makes these local isomorphisms compatible, so they glue; the glued inverse
is obtained from the local inverses. Uniqueness follows because morphisms
of schemes are determined on an affine open cover.

## Compatibility of the local structure maps

On every overlap, the two local structure maps to $X$ agree after applying
the constructed overlap map $\omega_{ij}$.

*Proof.*
On a basic refinement, both composites are the structural map from the
blow-up of the localized ideal to $D(s)\subseteq X$; the degree-zero part of
the restriction isomorphism makes them equal. Equality on the basic cover
gives equality on the overlap.

## Global blow-up morphism

Define

$$
b_{X,\mathcal I}\colon\operatorname{Bl}_{\mathcal I}(X)\longrightarrow X
$$

by gluing the local structure maps
$\mathsf B_{V_i}(\mathcal I)\to V_i\to X$. Their overlap equality is
[prop-nagata-global-blowup-cover-independent], so the morphism-gluing
interface applies.

## Affine-restriction comparison for the global blow-up

If $V=\operatorname{Spec}(A)\subseteq X$ and $I_V$ represents
$\mathcal I|_V$, define

$$
q_V\colon b_{X,\mathcal I}^{-1}(V)\longrightarrow
\operatorname{Bl}_{I_V}(\operatorname{Spec}A)
$$

by gluing the affine restriction maps on the basic intersections of $V$
with the chosen affine cover of $X$.

## Comparison between two affine-cover constructions

Given two affine covers of $X$, choose their intersection refinement. On
every refined affine chart use the two affine-restriction isomorphisms to
define a comparison, and glue these comparisons after transporting them to
the original charts. The overlap equalities are those of
[lemma-nagata-global-blowup-overlap-cocycle].
The refinement maps are independent of the selected basic chart by the
overlap cocycle, so the glued comparison is well-defined as a morphism of
the two gluing data.

## Affine restriction of the global blow-up

The constructed comparison $q_V$ is an isomorphism over $V$.

*Proof.*
Cover $V$ by basic opens contained in the chosen affine charts. On each,
the comparison is an isomorphism by
[prop-nagata-affine-blowup-restrict]; the overlap cocycle and local-map
compatibility show that these maps and their inverses agree. The gluing
theorem therefore produces mutually inverse global morphisms over $V$.
