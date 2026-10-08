+++
id = "lemma-nagata-strict-transform-chart-closed"
kind = "lemma"
title = "Closedness of the strict-transform chart"
order = 145
uses = ["def-nagata-strict-transform-chart-ring", "lemma-nagata-power-torsion-submodule"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The quotient map
$C_a(A,B,I)\to C_a^{\mathrm{st}}(A,B,I)$ defines a closed immersion of
the strict-transform chart into the ordinary base-change chart.

## Proof

The power-torsion subset is an ideal by
[lemma-nagata-power-torsion-submodule], applied to the regular module
$C_a(A,B,I)$. The spectrum of a quotient ring is a closed subscheme.
