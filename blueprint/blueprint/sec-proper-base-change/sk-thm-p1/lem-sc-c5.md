+++
id = "lem-sc-c5"
kind = "lemma"
title = "C5: finiteness on proper curves"
order = 1116
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "lem-sc-artin-schreier-dimension", "lem-sc-as-sequence", "lem-sc-cohomological-dimension", "lem-sc-fixed-points-finite", "thm-sc-proper-cohomology"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth proper connected curve over $k$, let
$r$ be a prime (arbitrary, possibly
$r=\operatorname{char}k$), and let
$\mathbf F_r$ be the constant sheaf, viewed as constructible. Then
$\mathbf F_r$ satisfies $\mathcal C_5(C,\mathbf F_r)$ of
[def-weil-pbc-eight-curve-assertions]: $H^q(C_{\Et},\mathbf F_r)$
is finite for every $q\geq0$.

## Proof

If $r\neq\operatorname{char}k$, the finiteness is the explicit
computation of [thm-sc-proper-cohomology] and the vanishing for
$q>2$, which is [lem-sc-cohomological-dimension]. If
$r=\operatorname{char}k=p>0$, then $H^q(C,\mathbf F_p)=0$ for
$q>1$ by the Artin–Schreier bound
([lem-sc-artin-schreier-dimension]),
$H^0(C,\mathbf F_p)=\mathbf Z/p\mathbf Z$, and
$H^1(C,\mathbf F_p)=\ker(\wp:H^1(C,\mathcal O_C)\to H^1(C,\mathcal O_C))$ by the Artin–Schreier sequence
([lem-sc-as-sequence]), an $\mathbf F_p$-vector space of
dimension at most $g$ by [lem-sc-fixed-points-finite],
hence finite.
