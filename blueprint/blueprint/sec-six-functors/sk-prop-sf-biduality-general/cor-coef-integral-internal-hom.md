+++
id = "cor-coef-integral-internal-hom"
kind = "theorem"
title = "Integral constructible internal Hom"
order = 2147
tags = ["latex:corollary"]
uses = ["cor-weil-finite-constructible-hom", "lem-coef-integral-hom-reduction", "lem-coef-integral-residue-tor"]
+++
For $K,L\in D^b_c(X,R)$, the ambient
$R\mathcal Hom_R(K,L)$ lies in $D^b_c(X,R)$ and its
reductions are the corresponding finite internal Homs. If the
reduction Tor intervals of $K,L$ are $[a,b]$, $[c,e]$
and $\dim X\leq d$, one output interval is
$[c-b-2d,e-a+2d]$.

## Proof

Completeness and the canonical reductions follow from
[lem-coef-integral-hom-reduction]. The input reductions are
finite-Tor by [lem-coef-integral-residue-tor]. Their internal
Homs are constructible with the stated uniform bound by
[cor-weil-finite-constructible-hom]. These are exactly the
remaining conditions on the integral output.
