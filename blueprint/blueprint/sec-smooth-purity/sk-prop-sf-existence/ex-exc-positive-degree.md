+++
id = "ex-exc-positive-degree"
kind = "remark"
title = "Positive cohomology of a closed exceptional image"
order = 1805
tags = ["latex:example"]
uses = ["def-sc-curves", "def-weil-derived-cohomology-sheaves", "def-weil-pbc-direct-image", "lem-exc-closed-ambient", "lem-exc-closed-support-triangle", "prop-weil-pbc-strict-henselization-stalk-formula"]
+++
Let $k$ be an algebraic closure of a finite field of characteristic
$p$, let $T=\mathbf A^1_k$, a
smooth curve, and let $i:\{0\}\hookrightarrow T$.
For nonzero $A=A_{E,n}$ with $\ell\neq p$, the
cohomology sheaf
$\mathcal H^2(Ri^!A_T)$ is nonzero. Thus no bound
$Ri^!D^{[a,b]}\subseteq D^{[a-c,b]}$ is possible for this map.
The support triangle uses the
derived direct image of the
complement.

## Proof

Let $j= T\setminus\{0\}\hookrightarrow T$.
The long exact sequence of the triangle of
[lem-exc-closed-support-triangle], for the right adjoint $Ri^!$
of [lem-exc-closed-ambient], gives
$i_*\mathcal H^2(Ri^!A_T)=R^1j_*A_U$, since $A_T$
has no positive cohomology. By
[prop-weil-pbc-strict-henselization-stalk-formula], the stalk
of its right side at zero is the first Galois cohomology of the
fraction field of the strict local ring. In the two-term calculation
of [lem-exc-dvr-galois], the constant module has trivial action,
so this group is the cokernel of $A\xrightarrow{0}A$, namely
$A\neq0$. This proof of nonvanishing uses no smooth-purity
formula.
