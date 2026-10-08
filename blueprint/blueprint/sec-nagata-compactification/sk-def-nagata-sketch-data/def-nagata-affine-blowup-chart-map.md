+++
id = "def-nagata-affine-blowup-chart-map"
kind = "definition"
title = "Canonical affine blow-up chart morphism"
order = 33
lean = ["AlgebraicGeometry.AffineBlowup.chart"]
uses = ["def-nagata-affine-blowup", "def-nagata-homogeneous-away-to-chart", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
Define

$$
\chi_a\colon \operatorname{Spec}(A[I/a])\longrightarrow D_+(at)
$$

to be the affine morphism induced contravariantly by $\theta_a$ after the
standard identification of $D_+(at)$ with the spectrum of the degree-zero
homogeneous localization.
