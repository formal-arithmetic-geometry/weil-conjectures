+++
id = "cor-pur-finite-stage-smooth-dualizing-complex"
kind = "theorem"
title = "Finite-stage smooth dualizing complex"
order = 2029
tags = ["latex:corollary"]
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-smooth-trace", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-finite-coefficient-smooth-purity", "thm-pur-trace-normalization-transitivity"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and let $a_X:X\to\Spec k$ be a
separated finite-type,
smooth morphism of pure dimension $d$. The dualizing complex

$$
\omega_X=Ra_X^!A
$$

has the canonical identification

$$
\omega_X\xrightarrow{\ \sim\ }A_X(d)[2d],
$$

coming from [thm-pur-finite-coefficient-smooth-purity], and the counit
$Ra_{X!}\omega_X\to A$ is the normalized integration map

$$
R\Gamma_c(X,A_X(d)[2d])\longrightarrow A
$$

of [thm-pur-trace-normalization-transitivity], sending the
fundamental class of the $d$-dimensional oriented fiber to $1$.

## Proof

Apply [thm-pur-finite-coefficient-smooth-purity] to $f=a_X$ and
$K=A$: its source $La_X^*A(d)[2d]$ is $A_X(d)[2d]$, giving the
identification of the dualizing complex. Under this identification the
counit $Ra_{X!}Ra_X^!A\to A$ is, by [def-pur-smooth-trace], the
smooth trace
$\operatorname{Tr}^{\mathrm{sm}}_{a_X,A}$, whose normalization is
[thm-pur-trace-normalization-transitivity] in the case
$Y=\Spec k$.
