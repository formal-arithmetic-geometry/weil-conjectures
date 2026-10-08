+++
id = "def-nagata-affine-proj"
kind = "definition"
title = "Affine Proj"
order = 10
lean = ["AlgebraicGeometry.Proj"]
uses = ["def-nagata-homogeneous-localization-degree-zero"]
+++
For an $\mathbb N$-graded commutative ring $R$, use the Mathlib scheme
$\operatorname{Proj}(R)$, with its structural morphism to the degree-zero
spectrum. On a homogeneous element $f$ of positive degree, its standard
open is identified with $\operatorname{Spec}(R_{(f),0})$ by
`Proj.basicOpenIsoSpec`; a homogeneous family generating the
irrelevant ideal gives the cover through
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`.
