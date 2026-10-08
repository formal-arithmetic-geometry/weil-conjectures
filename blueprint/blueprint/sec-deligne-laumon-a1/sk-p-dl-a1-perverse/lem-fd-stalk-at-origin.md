+++
id = "lem-fd-stalk-at-origin"
kind = "lemma"
title = "Stalk of the transform at the origin of the dual line"
order = 2746
uses = ["def-fd-kernel", "def-fd-transform", "def-weil-ordinary-compact-cohomology", "lem-fd-stalk-formula"]
+++
Let $K_0$ be a Weil complex on $\mathbf A^1_{k_0}$ (in the
conventions of [def-fd-transform]) and let $0'$ be the origin of
the dual line $V^\vee$. In the compact-support convention of
[def-weil-ordinary-compact-cohomology] there is a canonical
isomorphism

$$
\bigl(\operatorname{FT}_\psi(K)\bigr)_{0'}\;\cong\;R\Gamma_c\bigl(\mathbf A^1_{k_0},K\bigr)[1].
$$

In particular, for the middle extension
$K=j_{!*}\mathcal M[1]=j_*\mathcal M[1]$ of a lisse sheaf
$\mathcal M$ on $U_0\subset\mathbf A^1_{k_0}$, the stalk at
$0'$ has exactly two possibly nonzero cohomology groups, in degrees
$-1$ and $0$:

$$
\mathcal H^{-1}\bigl(\operatorname{FT}_\psi(j_*\mathcal M[1])_{0'}\bigr)
\cong H_c^1(\mathbf A^1_{k_0},j_*\mathcal M),
\qquad
\mathcal H^0\bigl(\operatorname{FT}_\psi(j_*\mathcal M[1])_{0'}\bigr)
\cong H_c^2(\mathbf A^1_{k_0},j_*\mathcal M).
$$

## Proof

By the stalk formula of [lem-fd-stalk-formula], for the geometric
point over the origin $0'$ of the dual line the kernel factor is
$\mathcal L_{\psi(x\cdot0)}=\mathcal L_{\psi(0)}$, the constant
sheaf (the Artin–Schreier sheaf of the zero function, the unit of the
kernel family of [def-fd-kernel]); hence

$$
\bigl(\operatorname{FT}_\psi(K)\bigr)_{0'}
=\mathcal H^*_c\bigl(\mathbf A^1_{k_0},K\otimes^L\mathcal L_{\psi(0)}\bigr)[1]
=R\Gamma_c(\mathbf A^1_{k_0},K)[1].
$$

For $K=j_*\mathcal M[1]$ this complex is
$R\Gamma_c(\mathbf A^1_{k_0},j_*\mathcal M)[2]$, and the
compact-support cohomology (the convention of
[def-weil-ordinary-compact-cohomology]) of the constructible sheaf
$j_*\mathcal M$ on the affine line is concentrated in degrees
$0,1,2$: of these the degree-zero group vanishes (a compactly
supported global section is zero by the lissity argument), so the
possibly nonzero cohomology groups sit in degrees $1$ and $2$ of
$R\Gamma_c$, hence in degrees $-1$ and $0$ after the shift by
$[2]$, with the displayed identifications.
