+++
id = "lemma-nagata-homogeneous-away-to-chart"
kind = "lemma"
title = "Well-definedness of the homogeneous-localization chart map"
order = 30
uses = ["def-nagata-homogeneous-away-to-chart", "lemma-nagata-chart-ring-fraction-equality"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

The assignment $\theta_a$ is independent of the chosen homogeneous
representative and defines a ring homomorphism from the degree-zero
homogeneous localization to $A[I/a]$.

## Proof

Multiplication and addition are compatible with the displayed formula.
Well-definedness follows from
[lemma-nagata-chart-ring-fraction-equality], applied to the equality
relation in homogeneous localization after forgetting the grading.
