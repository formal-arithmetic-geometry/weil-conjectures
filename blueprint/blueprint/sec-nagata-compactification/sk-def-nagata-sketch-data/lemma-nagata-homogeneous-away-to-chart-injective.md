+++
id = "lemma-nagata-homogeneous-away-to-chart-injective"
kind = "lemma"
title = "Injectivity of the chart map"
order = 32
uses = ["lemma-nagata-chart-ring-fraction-equality", "lemma-nagata-homogeneous-away-to-chart"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

The constructed map $\theta_a$ is injective.

## Proof

If $x/a^n$ is zero in $A_a$, then $a^N x=0$ for some $N$. Multiplying the
homogeneous numerator and denominator by $(at)^N$ shows that the original
homogeneous fraction is zero.
