+++
id = "sbc-thm-algebraically-closed-invariance"
kind = "theorem"
title = "Invariance under extension of algebraically closed fields"
order = 1412
uses = ["def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "thm-sc-constant-invariance"]
+++
Let $k\subseteq k'$ be algebraically closed, let $C$ be a
smooth separated curve
over $k$, and let $d\geq1$ be prime to $\operatorname{char}k$. For
every $q\geq0$ the pullback map

$$
H^q(C_{\Et},\mathbf Z/d\mathbf Z)
\xrightarrow{\ \sim\ }H^q((C_{k'})_{\Et},\mathbf Z/d\mathbf Z)
$$

is an isomorphism.
(*the Jacobian chapter, [thm-sc-constant-invariance] (= Lemma
59.83.12, [Tag `0A5E`](https://stacks.math.columbia.edu/tag/0A5E) of Stacks Project for the corresponding
statement).*)

## Proof

This is [thm-sc-constant-invariance] of the Jacobian chapter (applied with
$n=d$), which proves the same assertion for the constant sheaf
$\mathbf F_d$; this is the displayed pullback map by the definition of
the etale cohomology of [def-weil-pbc-etale-cohomology].
