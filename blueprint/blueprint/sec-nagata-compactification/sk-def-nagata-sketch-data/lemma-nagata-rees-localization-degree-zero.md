+++
id = "lemma-nagata-rees-localization-degree-zero"
kind = "lemma"
title = "Compatibility with degree zero"
order = 41
uses = ["lemma-nagata-rees-degree-zero", "prop-nagata-rees-localization"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

On degree zero, the constructed coefficientwise localization map is the standard ring
equivalence $A_s\otimes_AA\cong A_s$.

## Proof

Evaluate both maps on a constant monomial and use ring-homomorphism
extensionality.
