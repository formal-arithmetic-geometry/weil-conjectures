+++
id = "cor-weil-pbc-geometric-fiber-finite"
kind = "theorem"
title = "Finite-coefficient geometric-fiber formula"
order = 1322
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-scheme-conventions", "prop-weil-proet-finite-proper-base-change"]
tags = ["latex:corollary"]
+++
Let $f:X\to Y$ be proper, let $\bar y:\operatorname{Spec}\Omega\to Y$ be
geometric, and let $i_{\bar y}:X_{\bar y}\to X$ and $a_{\bar y}:X_{\bar
y}\to\operatorname{Spec}\Omega$ be the projections. Let $\Lambda$ be a finite
ring and let $K\in\Dplus(X_{\Et},\Lambda)$. The etale base-change morphism is
an isomorphism

$$
 \bar y^{-1}Rf_*K\xrightarrow{\sim}
 Ra_{\bar y,*}i_{\bar y}^{-1}K.
$$

For a finite $\Lambda$-module sheaf $F$ this gives, for every $q\geq0$,

$$
 (R^qf_*F)_{\bar y}\xrightarrow{\sim}
 H^q(X_{\bar y},F|_{X_{\bar y}}).
$$

## Proof

Specialize [prop-weil-proet-finite-proper-base-change] to the cartesian square
[def-weil-pbc-cartesian-square] defined by the geometric point $\bar y$, whose
base change is $\operatorname{Spec}\Omega\to Y$; the second formula is the
cohomological consequence for the sheaf $F$ placed in degree zero.
