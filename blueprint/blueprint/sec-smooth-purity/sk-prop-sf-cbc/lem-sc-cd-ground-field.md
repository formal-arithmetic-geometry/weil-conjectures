+++
id = "lem-sc-cd-ground-field"
kind = "lemma"
title = "Descent of a geometric cohomological dimension bound"
order = 1548
uses = ["def-sc-etale-torsion-cd", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-cohomology-filtered-colimit", "lemma-weil-pbc-torsion-filtered-union", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-sp-grothendieck", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $X$ be a finite-type
scheme over a field $K$, and let $\overline K$ be an algebraic
closure. If $\operatorname{cd}_{\rm tor}(K)\leq c$ and
$\operatorname{cd}_{\rm tor}(X_{\overline K})\leq e$, then
$\operatorname{cd}_{\rm tor}(X)\leq c+e$, using
[def-sc-etale-torsion-cd].

## Proof

For the structure map $f:X\to\operatorname{Spec}K$, the stalk
formula [prop-weil-pbc-strict-henselization-stalk-formula]
identifies the unique geometric stalk of $R^qf_*F$ with
$H^q(X_{K^{\rm sep}},F|)$. Passing from $K^{\rm sep}$ to
$\overline K$ is a purely inseparable algebraic extension,
whose base change is a universal homeomorphism.
Thus [thm-weil-pbc-universal-homeomorphism-invariance]
makes this group zero for $q>e$.
For $F$ killed by $n$, every $R^qf_*F$ is also killed by
$n$. The spectral sequence of [thm-sp-grothendieck]
has terms $H^p(K,R^qf_*F)$, zero unless $p\leq c$ and
$q\leq e$; its total degrees are at most $c+e$.
For arbitrary torsion $F$, pass to the union of the $F[n]$
using [lemma-weil-pbc-torsion-filtered-union], [lem-weil-pbc-cohomology-filtered-colimit].
