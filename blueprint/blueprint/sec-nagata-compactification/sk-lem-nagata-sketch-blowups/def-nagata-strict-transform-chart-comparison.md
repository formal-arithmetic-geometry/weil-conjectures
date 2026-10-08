+++
id = "def-nagata-strict-transform-chart-comparison"
kind = "definition"
title = "Strict-transform chart comparison"
order = 150
uses = ["def-nagata-strict-chart-to-extended-blowup-chart", "def-nagata-strict-transform-chart-ring"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

Define

$$
\overline\sigma_a\colon
C_a^{\mathrm{st}}(A,B,I)\longrightarrow B[IB/b]
$$

to be the map induced by $\sigma_a$ on the power-torsion quotient.
