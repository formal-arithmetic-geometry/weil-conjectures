+++
id = "cor-rp-euler-product"
kind = "theorem"
title = "Euler product of the $L$-function of a lisse sheaf"
order = 2663
tags = ["latex:corollary"]
uses = ["d-real-cohom", "def-weil-punctual-weights", "def-wf-weil-category", "lem-a1-affine-hc0", "thm-trf-grothendieck-lefschetz-qbar", "thm-trf-l-function-euler-product"]
+++
Let $U_0$ be a smooth geometrically connected affine curve, let
$U=U_0\times_{k_0}k$, and let $\mathcal G_0$ be a lisse
Weil sheaf on $U_0$. Then, as
power series in $t$ (the Euler series of [d-real-cohom]),

$$
\prod_{x\in|U_0|}\det\bigl(1-F_xt^{d(x)},\mathcal G_{0,\bar x}\bigr)^{-1}
=
\frac{\det(1-Ft,H_c^1(U,\mathcal G))}
{\det(1-Ft,H_c^2(U,\mathcal G))},
$$

where $|U_0|$ is the set of closed points, $d(x)$ the degree of
$x$, and the right-hand side is the graded form of the
Grothendieck–Lefschetz trace formula
[thm-trf-grothendieck-lefschetz-qbar] of the trace-formula chapter (summed
with the signs $(-1)^{i+1}$).

## Proof

This is the curve case of the Euler-product form of the trace formula
[thm-trf-l-function-euler-product], applied with $\Lambda=\Qlb$,
$X_0=U_0$ (separated of finite type, of dimension one) and
$K=\mathcal G_0$, a sheaf placed in degree zero, under the hypotheses
of [thm-trf-grothendieck-lefschetz-qbar] with which the trace formula
is applied to $\mathcal G_0$. The local factor of that theorem at a
closed point $x$ is $\det(1-F_xt^{e_x}\mid\mathcal G_{0,\bar x})$,
with $e_x=d(x)$ and $F_x$ the local geometric Frobenius at $x$ of
[def-weil-punctual-weights], so its $L(U_0,\mathcal G_0,t)$ is the
left-hand side; by its items (2) and (3) this equals

$$
\frac{\det(1-Ft,H_c^1(U,\mathcal G))}
{\det(1-Ft,H_c^0(U,\mathcal G))\,\det(1-Ft,H_c^2(U,\mathcal G))}.
$$

Finally $H_c^0(U,\mathcal G)=0$ by [lem-a1-affine-hc0], so the
factor $i=0$ is $1$, which gives the displayed identity.
