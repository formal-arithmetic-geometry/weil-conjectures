+++
id = "lemma-nagata-homogeneous-away-to-chart-surjective"
kind = "lemma"
title = "Surjectivity of the chart map"
order = 31
uses = ["lemma-nagata-chart-ring-normal-form", "lemma-nagata-homogeneous-away-to-chart"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

The constructed map $\theta_a$ is surjective.

## Proof

A normal-form element $x/a^n$ is the image of
$(xt^n)/(at)^n$.
