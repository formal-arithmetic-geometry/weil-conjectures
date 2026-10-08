+++
id = "sbc-thm-bounded-allowable-torsion"
kind = "theorem"
title = "Bounded allowable-torsion derived theorem"
order = 1438
uses = ["def-weil-pbc-hypercohomology-filtrations", "lemma-weil-pbc-geometric-stalk-conservative", "sbc-def-base-change-map", "sbc-def-base-change-square", "sbc-def-derived-categories-with-allowable-torsion", "sbc-lem-finite-range-comparison", "sbc-thm-smooth-base-change"]
+++
In the square of
[sbc-thm-smooth-base-change] with $f$ smooth, $g$ quasi-compact
and quasi-separated, and $\mathcal P$ the set of primes invertible on
$S$: for every $K\in D^b_{\mathcal P\text{-tor}}(T_{\Et})$, the
exchange map ${\operatorname{BC}}_{f,g}(K)$ of [sbc-def-base-change-map] is an
isomorphism in $D^b_{\mathcal P\text{-tor}}(S_{\Et})$ whenever both
sides are bounded, and is always an isomorphism in the ambient derived
category of abelian sheaves.

## Proof

Each $H^q(K)$ has geometric stalks that are torsion with prime divisors
in $\mathcal P$ ([sbc-def-derived-categories-with-allowable-torsion]);
[sbc-thm-smooth-base-change] applied to $H^q(K)$ makes the
comparison an isomorphism on every $E_2^{p,q}$ of
[def-weil-pbc-hypercohomology-filtrations]; $K$ is bounded, so
[sbc-lem-finite-range-comparison] transfers these isomorphisms to
the abutments; if both sides are bounded, this is the isomorphism in
$D^b_{\mathcal P\text{-tor}}(S_{\Et})$, and in general the detection on
cohomology sheaves of [lemma-weil-pbc-geometric-stalk-conservative]
gives the isomorphism in the ambient category.
