+++
id = "def-fd-kernel"
kind = "definition"
title = "The Fourier kernel and integrand"
order = 2691
lean = ["AlgebraicGeometry.Etale.fourierKernel"]
uses = ["def-fd-artin-schreier-sheaf", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions"]
+++
Let $S_0$ be a separated
scheme of finite type over $k_0$, let $V_0\to S_0$ be a vector
bundle of rank $r$ with dual $V_0^\vee$, and let

$$
b:V_0\times_{S_0}V_0^\vee\longrightarrow\mathbf A^1_{S_0},\qquad
(x,\xi)\longmapsto\langle x,\xi\rangle,
$$

be the evaluation pairing, a morphism of $S_0$-schemes; composed with
$\mathbf A^1_{S_0}\to\mathbf A^1_{k_0}$ it is a global function
$b\in\Gamma(V_0\times_{S_0}V_0^\vee,\mathcal O)$. The
*Fourier kernel* is the Artin–Schreier sheaf of [def-fd-artin-schreier-sheaf]
attached to this function,

$$
\mathcal K_\psi:=\mathcal L_{\psi,b}=b^*\mathcal L_\psi,
\qquad \mathcal L_\psi=\mathcal L_{\psi,x}\ \text{on }\mathbf A^1_{k_0},
$$

on $V_0\times_{S_0}V_0^\vee$; the two descriptions agree because the
Artin–Schreier covering of $f\circ h$ is the pullback along $h$ of the
covering of $f$, so $h^*\mathcal L_{\psi,f}=\mathcal L_{\psi,f\circ h}$.
For $K\in D^b_c(V,E)$ (the
coefficient category of [def-weil-pbc-qbar-category]), the
*Fourier integrand* is

$$
\mathcal F_\psi(K):=p_1^*K\otimes^L_E\mathcal K_\psi\in D^b_c(V\times_SV^\vee,E),
$$

with $p_1:V\times_SV^\vee\to V$ the first projection; the Fourier–Deligne
transform is its compact-support direct image along the second projection
$p_2$. (The triple product $V\times_SV^\vee\times_SV'$ with its projections
$r_{ij}$ is introduced separately, for the composition of kernel transforms.)
