+++
id = "cor-pur-adic-and-rational-smooth-dualizing-complexes"
kind = "theorem"
title = "Adic and rational smooth dualizing complexes"
order = 2030
tags = ["latex:corollary"]
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-smooth-trace", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-rational-and-qbar-purity", "thm-pur-trace-normalization-transitivity"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$\Lambda\in\{\mathcal O_E,E,\Qlb\}$, and let $a_X:X\to\Spec k$ be a
separated finite-type smooth morphism of pure dimension $d$. The
dualizing complex

$$
\omega_{X,\Lambda}=Ra_X^!\Lambda
$$

has the canonical identification

$$
\omega_{X,\Lambda}\xrightarrow{\ \sim\ }\Lambda_X(d)[2d]
$$

obtained from [thm-pur-rational-and-qbar-purity], and the counit
identifies with the transported normalized integration map

$$
R\Gamma_c(X,\Lambda_X(d)[2d])\longrightarrow\Lambda.
$$

## Proof

Apply [thm-pur-rational-and-qbar-purity] to $f=a_X$ and the
coefficient $\Lambda$: the purity isomorphism identifies the dualizing
complex with $\Lambda_X(d)[2d]$, and the counit is the transported smooth
trace [def-pur-smooth-trace], whose normalization is the
coefficient transport of
[thm-pur-trace-normalization-transitivity].
