+++
id = "lemma-nagata-chart-ring-fraction-equality"
kind = "lemma"
title = "Equality criterion for chart fractions"
order = 28
uses = ["lemma-nagata-chart-ring-normal-form"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

Two representatives $x/a^m$ and $y/a^n$ define the same element of
$A[I/a]$ exactly when they are equal in the localization $A_a$; equivalently,
some power of $a$ annihilates $a^nx-a^my$ after aligning denominators.

## Proof

This is the equality relation in localization away from the powers of $a$.
The statement must use localization equivalence, not cancellation by $a$,
because $a$ may be a zero divisor in $A$.
