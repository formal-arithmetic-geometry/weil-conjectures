+++
id = "lem-fd-inversion"
kind = "theorem"
title = "Fourier inversion"
order = 2716
lean = ["AlgebraicGeometry.Etale.fourierTransformInversionIso", "AlgebraicGeometry.Etale.fourierTransformSquareIso"]
uses = ["def-fd-transform", "def-wf-tate-twist", "lem-fd-convolution-kernel", "lem-fd-kernel-composition", "prop-functor-package"]
+++
Let $S=\Spec k$ (with $V\cong\mathbf A^r_k$ of rank $r$, and let
$\iota':V\to V$ be the inverse of the addition). For every
constructible Weil complex $K$ on $V$ there are functorial
isomorphisms

$$
\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi(K)\cong K(-r),
$$

and, with the same character,

$$
\operatorname{FT}_\psi\operatorname{FT}_\psi(K)\cong{\iota'}^*K(-r),
$$

where $(-r)$ is the $r$-fold Tate twist of [def-wf-tate-twist]
(exponent $r$: the relative dimension of the line, since the
compactly supported cohomology of the affine space
$\mathbf A^r_k$ carries the twist
$\overline{\mathbf Q}_\ell(-r)$ – the Poincare dual of the constant
sheaf
– in the top-degree contribution of the fibre integral; for $r=1$
this is the single twist $(-1)$).
(*Source: Fourier–Deligne inversion with geometric Frobenius and
the normalization $[r]$ of [def-fd-transform]; the same-kernel
calculation as the same-character square; Laumon, *Transformation
de Fourier*, (2.1.3), (2.5.6).*)

## Proof

By [lem-fd-kernel-composition] the composite
$\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi$ is the kernel
transform with kernel $\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi$ and shift
$[2r]$, and by [lem-fd-convolution-kernel] that kernel is
$\Delta_*\overline{\mathbf Q}_\ell(-r)[-2r]$. The kernel transform with
kernel $\Delta_*\overline{\mathbf Q}_\ell$ is the identity functor:
$\Delta$ is a closed immersion, so the projection formula of
[prop-functor-package] gives
$s_1^*K\otimes^L\Delta_*\overline{\mathbf Q}_\ell\cong\Delta_*K$, and
$s_{2,!}\Delta_*={(s_2)}_\Delta{}_!=\operatorname{id}_V$ because
$s_2\circ\Delta=\operatorname{id}_V$. Hence

$$
\operatorname{FT}_{\psi^{-1}}\operatorname{FT}_\psi(K)
\cong K(-r)[-2r][2r]=K(-r),
$$

the twist being that of [lem-fd-convolution-kernel] and the two shifts
cancelling. For the second formula the same computation with the
anti-diagonal kernel of [lem-fd-convolution-kernel] identifies
$\operatorname{FT}_\psi\operatorname{FT}_\psi$ with the pullback along
$\iota'$ of the identity transform, whence ${\iota'}^*K(-r)$.
