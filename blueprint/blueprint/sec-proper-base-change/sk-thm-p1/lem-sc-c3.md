+++
id = "lem-sc-c3"
kind = "lemma"
title = "C3: vanishing of p-primary torsion"
order = 1114
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "lem-sc-artin-schreier-dimension", "lem-sc-as-sequence", "lem-sc-lang-steinberg"]
+++
Let $k$ be algebraically closed with
$\operatorname{char}k=p>0$, let $C$ be a
smooth separated connected curve over $k$, and let
$n=p$. Then the constant sheaf $\mathbf F_p$ satisfies
$\mathcal C_3(C,\mathbf F_p)$ of
[def-weil-pbc-eight-curve-assertions]: for every $q>1$,
$H^q(C_{\Et},\mathbf F_p)=0$.

## Proof

The sheaf $\mathbf F_p$ is $p$-primary, and
[lem-sc-artin-schreier-dimension] gives the vanishing for
$q>1$: via the Artin–Schreier sequence
([lem-sc-as-sequence]) and the Lang–Steinberg surjectivity of
$\wp=F-1$ ([lem-sc-lang-steinberg]), the $p$-cohomological
dimension of a smooth connected curve over the algebraically closed field
$k$ is at most one.
