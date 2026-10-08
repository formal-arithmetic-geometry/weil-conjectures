+++
id = "prop-nagata-relative-proj-functoriality"
kind = "theorem"
title = "Restriction, base change, and functoriality of Proj"
order = 44
tags = ["latex:proposition"]
uses = ["def-nagata-relative-proj", "lemma-nagata-proj-chart-ring-cocycle", "lemma-nagata-relative-proj-exists"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

Relative Proj has the following properties.

1. Its restriction to an affine open $V$ is canonically
$\operatorname{Proj}(\Gamma(V,\mathcal A))$, compatibly on iterated
restrictions.
1. A degree-preserving equivalence of graded algebras inducing the
chosen degree-zero base identification induces an isomorphism of Proj.
1. A surjective degree-preserving morphism of graded algebras induces
a closed immersion in the opposite direction on Proj.
1. If $g\colon X'\to X$ is flat, then coefficientwise pullback gives a
canonical base-change isomorphism
$$
\operatorname{Proj}_{X'}(g^*\mathcal A)
\cong X'\times_X\operatorname{Proj}_X(\mathcal A).
$$

The same base-change construction is required for an arbitrary morphism
$X'\to X$ when the universal blow-up lift is formed; that unrestricted
comparison is recorded as a separate conditional interface below.

## Proof

For (1), use the restriction isomorphism in
[lemma-nagata-relative-proj-exists]; transitivity of coefficientwise
localization gives the iterated-restriction equality. For (2), on an affine
chart the graded equivalence carries each homogeneous denominator to a
homogeneous denominator and induces an isomorphism of the corresponding
degree-zero localizations, hence an isomorphism of standard affine opens.
These maps agree on overlaps by the localization cocycle and glue uniquely.
For (3), a surjection has surjective maps on every homogeneous localization;
the induced maps on degree-zero rings give closed immersions of all standard
affine opens, which glue to the asserted closed immersion. Finally, for
(4), on $V=\operatorname{Spec}(A)\subseteq X$, put
$C=\Gamma(V,\mathcal A)$, and on
$V'=\operatorname{Spec}(B)\subseteq X'$ over $V$, the chart at a
homogeneous $f$ is identified on both sides using

$$
(C_{(f),0})\otimes_A B
\xrightarrow{\sim}(B\otimes_A C)_{(f\otimes1),0},
\qquad (x/f^m)\otimes b\longmapsto (x\otimes b)/(f\otimes1)^m .
$$

To justify this without a hidden cancellation argument, identify the
degree-zero homogeneous localization with the filtered colimit
$\varinjlim_m C_{md}$ whose transition map is multiplication by $f$.
Tensor product commutes with this filtered colimit, giving the displayed
isomorphism (in fact without using flatness). On pure fractions its inverse
sends $(x\otimes b)/(f\otimes1)^m$ to $(x/f^m)\otimes b$. It is compatible
with further localization, so the chart isomorphisms glue, and their
structural maps identify the glued schemes over $X$. This proves all four
assertions.
