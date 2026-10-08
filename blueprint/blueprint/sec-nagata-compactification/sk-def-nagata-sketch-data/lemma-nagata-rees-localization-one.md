+++
id = "lemma-nagata-rees-localization-one"
kind = "lemma"
title = "Localization at one"
order = 42
uses = ["lemma-nagata-rees-sum-components", "prop-nagata-rees-localization"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

After the canonical identifications $A_1\cong A$, the Rees localization
equivalence at $1$ is the identity.

## Proof

Both the localization equivalence and the identity send each homogeneous
monomial $at^n$ to itself under $A_1\cong A$. Use
[lemma-nagata-rees-sum-components] and ring-homomorphism extensionality.
