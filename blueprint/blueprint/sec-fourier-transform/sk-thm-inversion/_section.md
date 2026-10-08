+++
id = "sk-thm-inversion"
kind = "section"
title = "P13: invertibility of the transform"
order = 2715
lean = ["AlgebraicGeometry.Etale.fourierTransformInversionIso", "AlgebraicGeometry.Etale.fourierTransformSquareIso"]
uses = ["sk-lem-kernel-composition", "sk-prop-convolution-kernel"]
+++
*Theorem (sketch).*

Let $V\cong\mathbf A^r_k$ and let $K$ be a constructible Weil complex on $V$;
let $\iota':V\to V$ be the reflection of the addition. Then there are
functorial isomorphisms

$$
\FT_{\psi^{-1}}\FT_\psi(K)\cong K(-r),\qquad
\FT_\psi\FT_\psi(K)\cong{\iota'}^*K(-r).
$$

(Blueprint lem:fd-inversion; proved here — the compiled
chapter admitted this statement as an input, but the convolution computation
below discharges it.)

## Proof

By P11 the composite $\FT_{\psi^{-1}}\FT_\psi$ is the kernel transform with
kernel $\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi$ and shift $[2r]$, and by P12
that kernel is $\Delta_*\underline{E}(-r)[-2r]$. The kernel transform with
kernel $\Delta_*\underline{E}$ is the identity functor: $\Delta$ is a closed
immersion, so the projection formula gives
$s_1^*K\otimes^L\Delta_*\underline{E}\cong\Delta_*K$, and
$s_{2,!}\Delta_*=({s_2}_{|\Delta})_!=\operatorname{id}_V$ because
$s_2\circ\Delta=\operatorname{id}_V$. Hence

$$
\FT_{\psi^{-1}}\FT_\psi(K)\cong K(-r)[-2r][2r]=K(-r),
$$

the twist being that of P12 and the two shifts cancelling. For the second
formula the same computation with the anti-diagonal kernel of P12 identifies
$\FT_\psi\FT_\psi$ with the pullback along $\iota'$ of the identity transform,
whence ${\iota'}^*K(-r)$. The only inputs are the six operations, the
affine-space computation of the exponential sheaf and Poincaré duality: no
weight theory is used.

Uses: [sk-lem-kernel-composition], [sk-prop-convolution-kernel]
