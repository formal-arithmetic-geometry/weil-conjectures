+++
id = "prop-nagata-proj-standard-open"
kind = "theorem"
title = "Standard affine opens of Proj"
order = 11
lean = ["AlgebraicGeometry.Proj.basicOpenIsoSpec", "AlgebraicGeometry.Proj.iSup_basicOpen_eq_top"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "lemma-nagata-proj-chart-ring-cocycle"]
+++
Each positive-degree homogeneous $f$ determines an open subscheme
$D_+(f)\subseteq\operatorname{Proj}(R)$ and a canonical isomorphism

$$
D_+(f)\cong\operatorname{Spec}(R_{(f),0}).
$$

If homogeneous elements $(f_i)$ generate $R_+$, the $D_+(f_i)$ cover
$\operatorname{Proj}(R)$.

## Proof

The standard-open isomorphism is `Proj.basicOpenIsoSpec`.
The cover assertion is
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`; its hypothesis
that the chosen homogeneous family generates the irrelevant ideal is the
assumption in the statement.
Thus no independently glued affine scheme is being used.
