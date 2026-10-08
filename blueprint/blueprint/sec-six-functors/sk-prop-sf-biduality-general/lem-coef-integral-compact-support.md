+++
id = "lem-coef-integral-compact-support"
kind = "lemma"
title = "Integral compact supports have the prescribed reductions"
order = 2135
uses = ["def-weil-integral-rational-qbar-compact-support", "lem-coef-integral-residue-tor", "lem-coef-normalized-dvr-effectivity", "lem-fix-compact-support-coefficient-change", "lem-sf-etale-direct-image-vanishing", "thm-cbc-finite-level-proetale", "thm-sf-direct-image-tor-amplitude"]
+++
Let $f:X\to Y$ be separated of finite type, with
$\dim X\leq d$. For $K\in D^b_c(X,R)$ with reduction
Tor interval $[a,b]$, the functor defined in
[def-weil-integral-rational-qbar-compact-support] satisfies

$$
Rf_!K\in D^b_c(Y,R),\qquad
(Rf_!K)\otimes_R^L A_n\cong Rf_{!,n}K_n.
$$

One uniform reduction Tor interval is $[a,b+2d]$. These are the
canonical compact-support coefficient comparisons.

## Proof

The input reductions have a common Tor interval by
[lem-coef-integral-residue-tor]. On a compactification
$f=\bar f j$, replace the compactifying scheme by the
scheme-theoretic closure of $X$. Its dimension is at most
$d$. Extension by zero preserves constructibility and the
Tor interval. The proper direct-image theorem
[thm-sf-direct-image-tor-amplitude], with the bound of
[lem-sf-etale-direct-image-vanishing], therefore gives
$[a,b+2d]$ for $R\bar f_*j_!K_n$.
The finite compact-support site comparison is
[thm-cbc-finite-level-proetale].

The coefficient maps of
[lem-fix-compact-support-coefficient-change] make these objects
a normalized tower. Apply
[lem-coef-normalized-dvr-effectivity]: its limit has exactly
the stated reductions, with their constructibility and uniform
bound. That limit is the definition in
[def-weil-integral-rational-qbar-compact-support]. Both its
counit comparison and the maps used above are induced by the same
coefficient maps, so the isomorphisms are the specified comparisons.
