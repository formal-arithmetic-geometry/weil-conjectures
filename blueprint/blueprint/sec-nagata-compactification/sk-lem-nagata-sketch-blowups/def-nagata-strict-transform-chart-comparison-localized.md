+++
id = "def-nagata-strict-transform-chart-comparison-localized"
kind = "definition"
title = "Localized strict-transform chart comparison"
order = 152
uses = ["def-nagata-strict-transform-chart-comparison"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

After localizing the base ring or a chart ring, define
$(\overline\sigma_a)_s$ by localizing the source and target of
$\overline\sigma_a$ and transporting along the canonical tensor-product
and iterated-localization associativity maps.
