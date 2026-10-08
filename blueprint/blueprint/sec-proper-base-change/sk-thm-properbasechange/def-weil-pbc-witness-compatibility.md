+++
id = "def-weil-pbc-witness-compatibility"
kind = "definition"
title = "Witness compatibility condition"
order = 1352
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-finite-level-amplification"]
+++
For such a cartesian square $\square$, write $\mathrm{WIT}(\square)$ if the
four finite-level functors of [def-weil-pbc-finite-level-amplification]
commute with the normalization isomorphisms for $P_{n+1}\to P_n$ and carry
compatible etale-origin witnesses [def-weil-pbc-etale-origin-witness] to
compatible etale-origin witnesses.

*Source note:* no Stacks Project entry states this predicate: the
etale-origin witnesses are the blueprint's device for Stacks' hypothesis in
Theorem 61.30.1 ([Tag 09C9](https://stacks.math.columbia.edu/tag/09C9)) that
$K\otimes^L_\Lambda\underline{\Lambda/I^n}$ be bounded below with cohomology
sheaves coming from the etale site. The per-level existence of such an
origin is Stacks' Lemma 61.29.2 ([Tag
09C2](https://stacks.math.columbia.edu/tag/09C2)) (4): for a constructible
$K$ on a quasi-compact $X$ there are $a,b$ with $K=\Rlim K_n$, each $K_n$ of
tor amplitude in $[a,b]$ with constructible cohomology sheaves, and
$K_n=\epsilon^{-1}L_n$ for some $L_n\in D_{ctf}(X_{\Et},\Lambda/I^n)$.
Difference: Stacks states this for a single object, and neither asserts that
the $L_n$ are compatible over $n$ nor tracks maps $\alpha_n$ as in
[def-weil-pbc-etale-origin-witness]; the blueprint adds the compatibility
predicate $\mathrm{WIT}(\square)$.
