+++
id = "lemma-nagata-chart-ring-normal-form"
kind = "lemma"
title = "Normal form in a chart algebra"
order = 27
uses = ["def-nagata-blowup-chart-ring"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

Every element of $A[I/a]$ is represented in $A_a$ by $x/a^n$ for some
$n\geq 0$ and $x\in I^n$.

## Proof

The generators have the required form with $n=1$. The set of such
fractions contains the image of $A$, and is closed under addition and
multiplication after replacing two denominators by a common power of $a$.
It therefore contains the generated subalgebra. Conversely,
$x\in I^n$ is a sum of products of $n$ elements of $I$, so $x/a^n$ belongs
to the generated algebra.
