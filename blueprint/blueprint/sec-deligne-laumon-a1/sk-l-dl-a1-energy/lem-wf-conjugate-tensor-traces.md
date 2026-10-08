+++
id = "lem-wf-conjugate-tensor-traces"
kind = "lemma"
title = "The conjugate-tensor trace identity"
order = 2761
uses = ["cor-rp-euler-product", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "lem-zl-log-det-identity"]
+++
Let $X_0$ be a smooth geometrically connected affine curve over
$k_0=\mathbf F_q$ (the separated finite-type conventions of
[def-weil-pbc-scheme-conventions]), let $\mathcal F$ be a lisse
Weil sheaf in the coefficient category of
[def-weil-pbc-qbar-category], and let
$\bar{\mathcal F}$ be the sheaf of the complex-conjugate
($\iota$-conjugate) local Frobenius eigenvalues. Then for every
$y\in X_0(k_m)$,

$$
\operatorname{Tr}\bigl(F_y\mid
(\mathcal F\otimes\bar{\mathcal F})_{\bar y}\bigr)
=
\bigl|\iota\operatorname{Tr}(F_y\mid\mathcal F_{\bar y})\bigr|^2
\in\mathbf R_{\ge0},
$$

and consequently the $L^2$-series of the trace function,

$$
\varphi_{\mathcal F}(t):=\sum_{m\ge1}\Bigl(\sum_{y\in X_0(k_m)}
\bigl|\iota\operatorname{Tr}(F_y\mid\mathcal F_{\bar y})\bigr|^2\Bigr)t^{m-1},
$$

is the logarithmic derivative $L'/L$ of the $L$-series

$$
L(t):=L(X_0,\mathcal F\otimes\bar{\mathcal F},t)
=\prod_{x\in|X_0|}
\det\bigl(1-F_xt^{d(x)},(\mathcal F\otimes\bar{\mathcal F})_{\bar x}\bigr)^{-1},
$$

the factorization being the Euler-product form of the
Grothendieck–Lefschetz trace formula on the affine curve.

## Proof

At a closed point $x$ the eigenvalue multiset of
$\mathcal F\otimes\bar{\mathcal F}$ in the coefficient category of
[def-weil-pbc-qbar-category] at $\bar x$ is the set of
products $\alpha_i\bar\alpha_j$ of the $\iota$-images of the
eigenvalues of $F_x$ on $\mathcal F_{\bar x}$, hence at a point
$y\in X_0(k_m)$ the trace of the tensor is
$\sum_i|\iota(\alpha_i^m)|^2=|\iota\operatorname{Tr}(F_y)|^2\ge0$.
The regrouping of the closed points over the $k_m$-points therefore
gives the logarithmic derivative of the Euler product: the coefficient
of $t^{m-1}$ in $L'/L$ is
$\sum_{y\in X_0(k_m)}\operatorname{Tr}(F_y\mid(\mathcal F\otimes\bar{\mathcal F})_{\bar y})$,
the same point-counting step as in the graded Euler-product identity
[cor-rp-euler-product], with the logarithm of the Frobenius determinant
[lem-zl-log-det-identity] carrying the logarithmic derivative of
the factors: for the Frobenius module
$(\mathcal F\otimes\bar{\mathcal F})_{\bar x}$ with $F=F_x$ it gives
$\log\det(1-TF)^{-1}=\sum_{n\ge1}\Tr(F^n)T^n/n$ in $\Qlb[[T]]$;
substituting $T\mapsto t^{d(x)}$ and applying $t\,\frac{d}{dt}$ gives
$t\,\frac{d}{dt}\log\det(1-F t^{d(x)})^{-1}
=\sum_{n\ge1}d(x)\Tr(F^n)t^{d(x)n}$, and applying the field
isomorphism $\iota$ coefficientwise transports this identity of formal
power series from $\Qlb[[t]]$ to $\mathbf C[[t]]$. The displayed identity follows, and the coefficients of
$\varphi_{\mathcal F}$ are nonnegative reals.
