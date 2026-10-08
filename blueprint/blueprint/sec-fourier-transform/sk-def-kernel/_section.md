+++
id = "sk-def-kernel"
kind = "section"
title = "The Fourier kernel and integrand"
order = 2690
lean = ["AlgebraicGeometry.Etale.fourierKernel"]
uses = ["sk-def-as", "sk-def-fourier-set"]
+++
*Definition (sketch).*

Let $V_0\to S_0$ be a vector bundle of rank $r$ with dual $V_0^\vee$ and
evaluation pairing

$$
b:V_0\times_{S_0}V_0^\vee\longrightarrow\Aone_{S_0},\qquad
(x,\xi)\longmapsto\langle x,\xi\rangle,
$$

a morphism of $S_0$-schemes; composed with $\Aone_{S_0}\to\Aone_{k_0}$ it is
a global function $b\in\Gamma(V_0\times_{S_0}V_0^\vee,\mathcal O)$. The
*Fourier kernel* is the Artin–Schreier sheaf of this function,

$$
\mathcal K_\psi:=\mathcal L_{\psi,b}=b^*\mathcal L_\psi
$$

on $V_0\times_{S_0}V_0^\vee$, where $\mathcal L_\psi=\mathcal L_{\psi,x}$ is
the Artin–Schreier sheaf on $\Aone_{k_0}$ of [sk-def-as]; the two
descriptions agree because the Artin–Schreier covering of $f\circ h$ is the
pullback along $h$ of the covering of $f$, so $h^*\mathcal L_{\psi,f}
=\mathcal L_{\psi,f\circ h}$. For $K\in\Dbc(V,E)$ the *Fourier
integrand* is

$$
\mathcal F_\psi(K):=p_1^*K\otimes^L_E\mathcal K_\psi\in\Dbc(V\times_SV^\vee,E),
$$

$p_1:V\times_SV^\vee\to V$ being the first projection; the transform
(sk-def-ft) is its compact-support direct image along the second
projection $p_2$. (The triple product $V\times_SV^\vee\times_SV'$ and its
projections $r_{ij}$ are only needed for the composition of kernel
transforms, P11.) On $\Aone$ ($r=1$,
$S_0=\Spec k_0$) the pairing is the product $b(x,\xi)=x\xi$ and
$\mathcal K_\psi=\mathcal L_{\psi(x\xi)}$. (Blueprint def:fd-kernel.)

Uses: [sk-def-as], [sk-def-fourier-set]
