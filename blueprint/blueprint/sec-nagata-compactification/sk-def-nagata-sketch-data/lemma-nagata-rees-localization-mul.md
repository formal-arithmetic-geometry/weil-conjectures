+++
id = "lemma-nagata-rees-localization-mul"
kind = "lemma"
title = "Iterated localization coherence"
order = 43
uses = ["prop-nagata-rees-localization"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

Localizing first at $s$ and then at $t$ gives the same graded equivalence as
localizing at $st$, after the canonical equivalence
$(A_s)_t\cong A_{st}$.

## Proof

Both maps send a homogeneous coefficient $x\in I^n$ to $x/1$ and commute
with the inclusions of the localized base ring. Graded ring-homomorphism
extensionality gives equality.
