+++
id = "sbc-thm-bounded-below-derived-smooth-base-change"
kind = "theorem"
title = "Bounded-below derived smooth base change"
order = 1440
uses = ["lem-weil-pbc-derived-stalk-conservative", "lemma-weil-pbc-geometric-stalk-conservative", "sbc-def-base-change-map", "sbc-def-base-change-square", "sbc-def-derived-categories-with-allowable-torsion", "sbc-lem-bounded-below-truncation-criterion", "sbc-thm-bounded-allowable-torsion", "sbc-thm-smooth-base-change"]
+++
In the square of
[sbc-thm-smooth-base-change] with $f$ smooth, $g$ quasi-compact
and quasi-separated, and $\mathcal P$ the set of primes invertible on
$S$: for $K\in D^+_{\mathcal P\text{-tor}}(T_{\Et})$,

$$
{\operatorname{BC}}_{f,g}(K):Lf^*Rg_*K\xrightarrow{\ \sim\ }Rh_*Le^*K
$$

in $D^+_{\mathcal P\text{-tor}}(S_{\Et})$.

## Proof

For each $n$ apply [sbc-thm-bounded-allowable-torsion] to
$\tau_{\leq n}K$ (bounded, allowable torsion) and use
[sbc-lem-bounded-below-truncation-criterion] to identify the
abutments; detection on cohomology sheaves
([lem-weil-pbc-derived-stalk-conservative], [lemma-weil-pbc-geometric-stalk-conservative]) gives the statement.
