+++
id = "def-nagata-strict-transform-chart-ring"
kind = "definition"
title = "Affine strict-transform chart ring"
order = 144
uses = ["def-nagata-power-torsion", "def-nagata-strict-transform-basechange-chart-ring"]
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
C_a^{\mathrm{st}}(A,B,I)
=C_a(A,B,I)/\Gamma_{(a)}(C_a(A,B,I)).
$$
