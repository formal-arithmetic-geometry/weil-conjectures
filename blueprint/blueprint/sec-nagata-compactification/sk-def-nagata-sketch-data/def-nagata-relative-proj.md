+++
id = "def-nagata-relative-proj"
kind = "definition"
title = "Relative Proj"
order = 12
uses = ["def-nagata-affine-proj"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

Let $X$ be a scheme and
$\mathcal A=\bigoplus_{n\geq0}\mathcal A_n$ a quasi-coherent graded
$\mathcal O_X$-algebra. On every affine open $V\subseteq X$, form

$$
\operatorname{Proj}(\Gamma(V,\mathcal A)).
$$

Quasi-coherence identifies the graded algebra on a basic affine restriction
with coefficientwise localization. The intended relative Proj is the scheme
obtained by gluing these affine Proj schemes along the induced standard-chart
equivalences, with structural map to $X$ glued from the degree-zero maps.
The construction includes the chosen affine cover, all overlap
isomorphisms, their cocycle equalities, and the resulting universal
restriction isomorphisms.
