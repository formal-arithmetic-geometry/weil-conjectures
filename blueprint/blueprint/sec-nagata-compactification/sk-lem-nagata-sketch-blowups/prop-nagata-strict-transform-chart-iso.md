+++
id = "prop-nagata-strict-transform-chart-iso"
kind = "theorem"
title = "Affine strict-transform chart formula"
order = 151
tags = ["latex:proposition"]
uses = ["def-nagata-strict-transform-chart-comparison", "lemma-nagata-strict-chart-map-kernel", "lemma-nagata-strict-chart-map-surjective"]
+++
**Status.** Bypassed by the formalized route: the strict transform is
supplied by the API of
`WeilConjectures/Compactification/StrictTransform.lean` —
`AlgebraicGeometry.strictTransform`, its closed immersion
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and the pullback square
`AlgebraicGeometry.isPullback_strictTransformOpen` — so the
strict-transform chart rings and their cocycle are never assembled by hand.

The constructed comparison $\overline\sigma_a$ is a ring equivalence.

## Proof

The map $\sigma_a$ is surjective and its kernel is precisely the ideal by
which the source was quotiented. The first isomorphism theorem therefore
makes $\overline\sigma_a$ bijective and identifies its inverse ring
structure, so it is a ring equivalence.
