+++
id = "lemma-nagata-localization-rees-piece"
kind = "lemma"
title = "Localization of each Rees piece"
order = 38
uses = ["lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-piece-membership"]
+++
**Status.** Bypassed by the formalized route: the affine blow-up and its
charts are the construction `AlgebraicGeometry.AffineBlowup`, with
`AffineBlowup.chart` and
`AffineBlowup.isLocalization_away_map` supplying the chart algebra
and its localization coherence, so neither is rebuilt by hand.

Flatness of $A\to A_s$ gives an $A_s$-linear equivalence

$$
A_s\otimes_A\mathcal R_A(I)_n
\cong\mathcal R_{A_s}(IA_s)_n
$$

for every $n$.

## Proof

Identify the two modules with
$A_s\otimes_AI^n$ and $(IA_s)^n$, then use exactness of localization and
[lemma-nagata-localization-ideal-pow].
