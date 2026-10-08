+++
id = "cor-trf-constant-stalk-trace"
kind = "theorem"
title = "Constant coefficients have unit stalk trace"
order = 2322
tags = ["latex:corollary"]
uses = ["def-trf-categorical-trace", "def-weil-derived-pullback-tensor-hom", "def-weil-site-perfect-complex", "lem-trf-chain-supertrace"]
+++
For the constant complex $K=A_X$ in degree zero and the canonical
map $u:Lh^*A_X\simeq A_X$, every fixed geometric stalk has
categorical trace equal to $1$.
The complex is site-perfect.

## Proof

The complex consists of a single free rank-one sheaf, so it satisfies
[def-weil-site-perfect-complex]. Pullback preserves the unit by
[def-weil-derived-pullback-tensor-hom]; its canonical map is the
identity on each rank-one stalk. The degree-zero chain trace in
[lem-trf-chain-supertrace] is therefore $1$.
