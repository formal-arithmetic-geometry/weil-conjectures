+++
id = "def-nagata-homogeneous-away-to-chart"
kind = "definition"
title = "Homogeneous-localization chart map"
order = 29
uses = ["def-nagata-blowup-chart-ring", "def-nagata-rees-algebra"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

For $a\in I$, define $\theta_a$ on a degree-zero homogeneous fraction by

$$
\theta_a\!\left(\frac{xt^n}{(at)^n}\right)=\frac{x}{a^n},
\qquad x\in I^n.
$$
