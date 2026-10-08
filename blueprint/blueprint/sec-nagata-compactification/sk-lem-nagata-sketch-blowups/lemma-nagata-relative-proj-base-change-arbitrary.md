+++
id = "lemma-nagata-relative-proj-base-change-arbitrary"
kind = "lemma"
title = "Relative Proj base change for an arbitrary morphism"
order = 107
uses = ["lemma-nagata-proj-chart-ring-cocycle", "prop-nagata-relative-proj-functoriality"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

For any morphism $g\colon Y\to X$ and graded quasi-coherent algebra
$\mathcal A$ on $X$, coefficientwise pullback gives a canonical isomorphism

$$
\operatorname{Proj}_Y(g^*\mathcal A)
\cong Y\times_X\operatorname{Proj}_X(\mathcal A).
$$

## Proof

Cover $X$ by affine opens $V=\operatorname{Spec}(A)$ and cover each affine
inverse image in $Y$ by $W=\operatorname{Spec}(B)$, with structure map
$A\to B$. Put $C=\Gamma(V,\mathcal A)$. For every positive-degree
homogeneous $f\in C$, the two standard charts in the asserted comparison
have coordinate rings

$$
B\otimes_A C_{(f),0}\quad\text{and}\quad
(B\otimes_A C)_{(f\otimes1),0}.
$$

For fixed $f$, the degree-zero homogeneous localization is the filtered
colimit of the modules $C_{m\deg(f)}$ under multiplication by $f$.
Since tensor product commutes with filtered colimits, there is a canonical
isomorphism

$$
B\otimes_A C_{(f),0}\;\xrightarrow{\sim}\;
(B\otimes_A C)_{(f\otimes1),0}.
$$

On pure fractions this isomorphism and its inverse are given by

$$
(b\otimes x/f^m)\longmapsto (b\otimes x)/(f\otimes1)^m,
\qquad
(b\otimes x)/(f\otimes1)^m\longmapsto b\otimes x/f^m
$$

and extend additively. The filtered-colimit description, rather than
injectivity after tensoring, proves that these formulas are well-defined and
mutually inverse for an arbitrary $A\to B$. They are compatible with
localization at a second homogeneous element, so the affine chart
isomorphisms agree on all overlaps. The standard opens cover both Proj
schemes, and `AlgebraicGeometry.Scheme.GlueData.glued` therefore
produces an
isomorphism

$$
\operatorname{Proj}_Y(g^*\mathcal A)\cong
Y\times_X\operatorname{Proj}_X(\mathcal A).
$$

The construction is natural in $g$ and in maps of graded algebras because
every displayed map is induced by tensor product and localization; hence it
is the required canonical arbitrary-base-change comparison.
