+++
id = "prop-nagata-strict-transform-closed-fiber-product"
kind = "theorem"
title = "Global strict transform is a closed subscheme"
order = 157
tags = ["latex:proposition"]
uses = ["def-nagata-strict-transform", "def-nagata-strict-transform-closed-chart-model", "lemma-nagata-strict-transform-chart-closed", "lemma-nagata-strict-transform-chart-cocycle", "lemma-nagata-strict-transform-chart-localization-data"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

Under the data of
[def-nagata-strict-transform-closed-chart-model], the constructed chart
model $Y^{\mathrm{st}}_{\mathrm{chart}}$ is a closed
subscheme of $Y\times_XX'$ and agrees with the strict transform of
[def-nagata-strict-transform].

## Proof

The chartwise closed immersions agree on overlaps by
[lemma-nagata-strict-transform-chart-cocycle]; therefore their ideals
glue to a global quasi-coherent ideal, with localization compatibility
supplied by [lemma-nagata-strict-transform-chart-localization-data].
On each chart the quotient removes
exactly the sections supported on the exceptional divisor, so the resulting
closed subscheme is the scheme-theoretic closure of the preserved open and
hence is the strict transform.
