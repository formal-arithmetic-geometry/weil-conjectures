+++
id = "def-nagata-flat-pullback-rees-map"
kind = "definition"
title = "Flat pullback map for Rees algebras"
order = 114
uses = ["def-nagata-extended-ideal", "def-nagata-sheaf-rees-algebra"]
+++
**Status.** Bypassed by the formalized route: blow-ups are never
base-changed along a flat morphism. Every base-change step the route takes
goes through the universal property
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_blowup` and
the chart pullback squares
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowup$\iota$`
instead.

For a quasi-coherent ideal $\mathcal I\subseteq\mathcal O_X$ and flat
$g\colon Y\to X$, define $\beta_g$ degreewise by the canonical
maps

$$
g^*(\mathcal I^n)\longrightarrow
(\mathcal I\mathcal O_Y)^n.
$$

Thus

$$
\beta_g\colon g^*\mathcal R_X(\mathcal I)\longrightarrow
\mathcal R_Y(\mathcal I\mathcal O_Y).
$$
