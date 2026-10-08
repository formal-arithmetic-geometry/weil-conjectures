+++
id = "lem-sc-c6"
kind = "lemma"
title = "C6: invariance under algebraically closed extension"
order = 1117
uses = ["def-sc-curves", "def-sc-field-extension", "def-weil-pbc-eight-curve-assertions", "thm-sc-constant-invariance"]
+++
Let $k\subseteq k'$ be algebraically closed, let $C$ be a
smooth separated connected curve over $k$, and let
$r$ be prime to $\operatorname{char}k$. Then the constant sheaf
$\mathbf F_r$ satisfies $\mathcal C_6(C,\mathbf F_r)$ of
[def-weil-pbc-eight-curve-assertions]: the pullback maps
$\rho^q_{k'/k}(C,\mathbf F_r)$ of [def-sc-field-extension] are
isomorphisms for every $q\geq0$.

## Proof

This is the invariant part of [thm-sc-constant-invariance]
(applied to $n=r$); the maps are the pullback maps of
[def-sc-field-extension] and agree with those fixed in
[def-weil-pbc-eight-curve-assertions].
