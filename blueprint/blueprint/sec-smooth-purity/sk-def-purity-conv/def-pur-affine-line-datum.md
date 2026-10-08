+++
id = "def-pur-affine-line-datum"
kind = "definition"
title = "The affine-line datum"
order = 1892
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-support-cohomology", "def-sbc-affine-space", "def-sbc-smooth-morphisms", "def-weil-derived-cohomology-sheaves", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-finite-kummer-level"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and let $Y$ be a
separated finite-type
$k$-scheme. Put

$$
\mathbf A^1_Y=\mathbf A^1_{\mathbf Z}\times_{\mathbf Z}Y
$$

for the affine line of [def-sbc-affine-space], with projection
$p:\mathbf A^1_Y\to Y$, zero section $s:Y\to\mathbf A^1_Y$ (the closed
immersion defined by the vanishing of the coordinate), and open complement

$$
j:\mathbf G_{m,Y}=\mathbf A^1_Y\setminus s(Y)\longrightarrow\mathbf A^1_Y.
$$

Let $t$ denote the global coordinate function on $\mathbf A^1_Y$, viewed
as a global unit on $\mathbf G_{m,Y}$. With
$N=n\cdot v_\ell(\varpi_E)$ as in [lem-pur-finite-kummer-level]
(whose hypothesis $e(E/\Ql)\mid n$ is assumed from now on), the
finite-level twist is

$$
A(1)_{\mathbf A^1_Y}
=\mu_{\ell^N,\mathbf A^1_Y}\otimes_{\mathbf Z/\ell^N}A,
$$

and the *Kummer class of $t$* is the class

$$
\kappa(t)\in H^1(\mathbf G_{m,Y},A(1))
$$

obtained from the Kummer sequence of etale sheaves of units
on $\mathbf G_{m,Y}$,

$$
0\longrightarrow\mu_{\ell^N}\longrightarrow\mathbf G_m
\xrightarrow{\ \ell^N\ }\mathbf G_m\longrightarrow0,
$$

whose boundary map $\mathbf G_m(Y)\cong H^0(\mathbf G_{m,Y},\mathbf G_m) \to H^1(\mathbf G_{m,Y},\mu_{\ell^N})$ is applied to the global unit
$t\in\Gamma(\mathbf G_{m,Y},\mathbf G_m)$, followed by the coefficient
extension $H^1(-,\mu_{\ell^N})\to H^1(-,A(1))$ induced by the canonical
isomorphism $A(1)\cong\mu_{\ell^N}\otimes_{\mathbf Z/\ell^N}A$ of
[lem-pur-finite-kummer-level]. (The naive tensor
$\mathbf G_m\otimes_{\mathbf Z/\ell^N}A$ of the Kummer sequence is not
defined at the level of sheaves: $\mathbf G_m$ is not a sheaf of
$\mathbf Z/\ell^N$-modules, as it contains elements of order not
dividing $\ell^N$; the $A$-coefficient form of the sequence is the
one obtained by extending coefficients on the $\mu_{\ell^N}$-term and
taking the connecting map, as above.) Equivalently, in *torsor
form*: the $\ell^N$-th root of the coordinate defines the finite etale
scheme

$$
\mathcal T_t=\operatorname{Spec}\mathcal O_{\mathbf G_{m,Y}}[T_0]
\bigm/\bigl(T_0^{\ell^N}-t\bigr),
$$

whose structure map $\mathcal T_t\to\mathbf G_{m,Y}$ is finite etale of
degree $\ell^N$ – the quotient is of finite presentation; $T_0$ is a
unit (the relation $T_0^{\ell^N}=t$ with $t$ a unit); and the
derivative $\ell^N T_0^{\ell^N-1}$ is a unit because $\ell^N$ is
invertible in the base field $k$ of [def-pur-conventions]
($\ell\neq p$ there) and $T_0$ is a unit, so the monogenic etale
criterion applies – and the multiplication of
$T_0$ by an $\ell^N$-th root of unity makes $\mathcal T_t$ a right
$\mu_{\ell^N,\mathbf G_{m,Y}}$-torsor; with $A$-coefficients,
$\mathcal T_t\otimes_{\mathbf Z/\ell^N}A$ is a right
$A(1)_{\mathbf G_{m,Y}}$-torsor, and $\kappa(t)$ is the class of this
torsor in $H^1(\mathbf G_{m,Y},A(1))$, the two descriptions being related
by the standard identification of the boundary of the Kummer sequence
with the torsor class. On the small pro-etale site,
the [def-weil-derived-cohomology-sheaves] cohomology sheaves of
the exceptional inverse
image along the zero section are written $R^r s^!(-)$, and the
supported cohomology of the pair $(s(Y),\mathbf A^1_Y)$ is that of
[def-pur-support-cohomology].
