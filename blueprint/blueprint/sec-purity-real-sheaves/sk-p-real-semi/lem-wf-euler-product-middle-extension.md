+++
id = "lem-wf-euler-product-middle-extension"
kind = "theorem"
title = "Graded Euler-product identity for a middle extension"
order = 2654
tags = ["latex:corollary"]
uses = ["d-real-cohom", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-qbar-category", "def-wf-middle-extension", "thm-trf-grothendieck-lefschetz-qbar", "thm-trf-l-function-euler-product"]
+++
Let $X_0$ be a smooth geometrically connected affine curve, let
$j:U_0\hookrightarrow X_0$ be a dense open immersion, and let
$\mathcal F$ be lisse on $U_0$ in the coefficient conventions of
[def-weil-pbc-qbar-category], with the middle extension
$j_*\mathcal F$ of
[def-wf-middle-extension]. As power series in $t$,

$$
\prod_{x\in|X_0|}\det\bigl(1-F_xt^{d(x)},(j_*\mathcal F)_{\bar x}\bigr)^{-1}
=
\frac{\det(1-Ft,H_c^1(X,j_*\mathcal F))}
{\det(1-Ft,H_c^2(X,j_*\mathcal F))},
$$

where the left-hand side is the $L$-series [d-real-cohom] of the constructible sheaf
$j_*\mathcal F$ on $X_0$ and the right-hand side is its graded form
in the compact-support convention of
[def-weil-ordinary-compact-cohomology].

## Proof

This is the curve case of the Euler-product form of the trace formula
[thm-trf-l-function-euler-product], applied with $\Lambda=\Qlb$ in
the coefficient category [def-weil-pbc-qbar-category], to the curve
$X_0$ (separated of finite type, of dimension one) and the
constructible sheaf $K=j_*\mathcal F$ placed in degree zero, under the
hypotheses of [thm-trf-grothendieck-lefschetz-qbar] with which the
trace formula is applied to it. Its $L(X_0,j_*\mathcal F,t)$ is the
left-hand side (the local factor at $x$ being
$\det(1-F_xt^{d(x)}\mid(j_*\mathcal F)_{\bar x})$, with $e_x=d(x)$),
and its items (2) and (3) give

$$
L(X_0,j_*\mathcal F,t)=
\frac{\det(1-Ft,H_c^1(X,j_*\mathcal F))}
{\det(1-Ft,H_c^0(X,j_*\mathcal F))\,\det(1-Ft,H_c^2(X,j_*\mathcal F))}.
$$

It remains to see that the degree-zero factor is $1$, i.e.
$H_c^0(X,j_*\mathcal F)=0$: a compactly supported global section of
$j_*\mathcal F$ vanishes in a neighborhood of every boundary point,
hence restricts to zero on the complement of its finite support in the
connected open curve, and by lissity it is zero.
