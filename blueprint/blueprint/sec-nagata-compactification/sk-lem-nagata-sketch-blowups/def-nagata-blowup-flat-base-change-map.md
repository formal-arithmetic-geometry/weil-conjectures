+++
id = "def-nagata-blowup-flat-base-change-map"
kind = "definition"
title = "Flat base-change comparison for blow-ups"
order = 116
uses = ["def-nagata-extended-ideal", "def-nagata-flat-pullback-rees-map", "def-nagata-global-blowup", "lemma-nagata-flat-pullback-rees", "prop-nagata-relative-proj-functoriality"]
+++
**Status.** Bypassed by the formalized route: blow-ups are never
base-changed along a flat morphism. Every base-change step the route takes
goes through the universal property
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup` and
the chart pullback squares
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowup$\iota$`
instead.

Let $g\colon Y\to X$ be flat and let
$\mathcal I\subseteq\mathcal O_X$ be a quasi-coherent ideal. With
$\mathcal I\mathcal O_Y$ defined in
[def-nagata-extended-ideal], define

$$
\operatorname{bc}_g\colon
\operatorname{Bl}_{\mathcal I\mathcal O_Y}(Y)
\longrightarrow
Y\times_X\operatorname{Bl}_{\mathcal I}(X)
$$

by applying relative Proj to $\beta_g$ on affine opens and gluing. The
degreewise graded equivalence used in this construction is
[lemma-nagata-flat-pullback-rees].
