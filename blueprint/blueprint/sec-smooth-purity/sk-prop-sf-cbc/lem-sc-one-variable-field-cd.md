+++
id = "lem-sc-one-variable-field-cd"
kind = "lemma"
title = "One-variable fields over a separably closed field"
order = 1549
uses = ["def-sc-etale-torsion-cd", "lem-sc-arbitrary-curve-cd", "lem-sc-cd-affine-limit", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
If $F$ is separably closed, then
$\operatorname{cd}_{\rm tor}(F(x))\leq1$, with the bound of
[def-sc-etale-torsion-cd].

## Proof

The field $F(x)$ is the filtered union of
$F[x,1/h]$, for nonzero $h\in F[x]$.
Each corresponding scheme is an affine curve.
The algebraic closure $\overline F/F$ is purely inseparable,
so its base change preserves the etale topos by
[thm-weil-pbc-universal-homeomorphism-invariance].
Over $\overline F$ the bound is one by
[lem-sc-arbitrary-curve-cd].
Use [lem-sc-cd-affine-limit] to pass to the fraction field.
