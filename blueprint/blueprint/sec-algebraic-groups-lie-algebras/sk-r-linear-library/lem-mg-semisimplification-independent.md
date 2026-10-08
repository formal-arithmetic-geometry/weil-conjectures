+++
id = "lem-mg-semisimplification-independent"
kind = "lemma"
title = "Semisimplification is independent of the composition series"
order = 2543
uses = ["def-mg-weil-composition-series", "def-mg-weil-semisimplification", "lem-mg-jordan-holder"]
+++
Let $V$ be a finite-dimensional Weil representation carrying two
composition series
$V_\bullet$ and $W_\bullet$, with semisimplifications
$V^{\mathrm{ss}}$ and $W^{\mathrm{ss}}$ as in
[def-mg-weil-semisimplification]. Then
$V^{\mathrm{ss}}$ and $W^{\mathrm{ss}}$ are isomorphic as Weil
representations.

## Proof

By [lem-mg-jordan-holder] the composition factors of
$V_\bullet$ and of $W_\bullet$, described in
[def-mg-weil-composition-series], agree up to permutation,
isomorphism and multiplicity. The two semisimplifications of
[def-mg-weil-semisimplification] are the direct sums of these two
families of Weil-stable quotients, so a bijection of the index sets
carrying each quotient to an isomorphic one extends to an isomorphism
$V^{\mathrm{ss}}\to W^{\mathrm{ss}}$ of the underlying vector spaces
commuting with the Weil actions.
