+++
id = "lem-sc-c1"
kind = "lemma"
title = "C1: vanishing above degree two"
order = 1112
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves", "lem-sc-cohomological-dimension"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth separated connected curve over $k$, and let
$n$ be a prime. Then the constant sheaf
$\mathbf F_n$ (see [def-weil-pbc-etale-sheaves]) satisfies
$\mathcal C_1(C,\mathbf F_n)$ of
[def-weil-pbc-eight-curve-assertions]: $H^q(C_{\Et},\mathbf F_n)=0$
for every $q>2$.

## Proof

The sheaf $\mathbf F_n$ is torsion; the assertion is
[lem-sc-cohomological-dimension] applied to it.
