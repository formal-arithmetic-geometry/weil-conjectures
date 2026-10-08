+++
id = "lemma-nagata-strict-transform-chart-localization"
kind = "lemma"
title = "Strict-transform chart formula localizes"
order = 153
uses = ["def-nagata-strict-transform-chart-comparison-localized", "lemma-nagata-power-torsion-localization", "prop-nagata-strict-transform-chart-iso"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The constructed localized comparison $(\overline\sigma_a)_s$ equals the
strict-transform chart comparison constructed directly from the localized
data.

## Proof

Localization commutes with the tensor product and with the power-torsion
quotient by [lemma-nagata-power-torsion-localization]. Both maps send
every pure tensor and every generator $x/a$ to the same fraction. Ring-map
extensionality gives the equality, and
[prop-nagata-strict-transform-chart-iso] supplies the equivalence
property on both sides.
