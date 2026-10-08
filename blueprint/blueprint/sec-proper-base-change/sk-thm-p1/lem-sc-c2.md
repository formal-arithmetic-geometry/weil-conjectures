+++
id = "lem-sc-c2"
kind = "lemma"
title = "C2: vanishing on affine curves"
order = 1113
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "lem-sc-affine-cohomological-dimension", "lem-sc-artin-schreier-dimension", "thm-sc-affine-cohomology"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth affine connected curve over $k$, and let
$n$ be a prime. Then the constant sheaf $\mathbf F_n$ satisfies
$\mathcal C_2(C,\mathbf F_n)$ of
[def-weil-pbc-eight-curve-assertions]: $H^q(C_{\Et},\mathbf F_n)=0$
for every $q>1$.

## Proof

If $n\neq\operatorname{char}k$, this is
[thm-sc-affine-cohomology]. If $n=\operatorname{char}k=p>0$,
then $\mathbf F_p$ is $p$-primary and the assertion follows from
[lem-sc-artin-schreier-dimension] (and
[lem-sc-affine-cohomological-dimension] directly).
