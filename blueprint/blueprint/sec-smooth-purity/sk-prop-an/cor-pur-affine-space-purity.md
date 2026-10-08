+++
id = "cor-pur-affine-space-purity"
kind = "theorem"
title = "Affine-space purity"
order = 1978
tags = ["latex:corollary"]
uses = ["def-coefficient-twists-detailed", "def-pur-affine-space-comparison", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "prop-pur-affine-space-composition-law", "thm-pur-affine-line-purity"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, let $d\geq0$, and let $K\in D^b_{ctf}(Y,\Lambda)$. The
comparison

$$
\gamma_{p_d,K}:Lp_d^*K(d)[2d]\xrightarrow{\ \sim\ }Rp_d^!K
$$

of [def-pur-affine-space-comparison] is an isomorphism.

## Proof

By induction on $d$: the case $d=0$ is the identity, and for
$d\geq1$ the composition law [prop-pur-affine-space-composition-law]
expresses $\gamma_{p_d,K}$ as the composite of the isomorphism
$\gamma_{p_{d-1},Rp_1^!K}$ (the induction hypothesis applied to the
$(d-1)$-fold affine space over the base-changed line) with the affine-line
purity isomorphism $\gamma_{p_1,K}$ of [thm-pur-affine-line-purity],
both conjugated by invertible reassociation isomorphisms; hence
$\gamma_{p_d,K}$ is an isomorphism.
