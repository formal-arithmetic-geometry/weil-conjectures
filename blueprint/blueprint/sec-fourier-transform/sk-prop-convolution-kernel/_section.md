+++
id = "sk-prop-convolution-kernel"
kind = "section"
title = "P12: the convolution of the kernels is the delta kernel"
order = 2713
lean = ["AlgebraicGeometry.Etale.fourierKernelConvolutionIso"]
uses = ["sk-lem-as-properties", "sk-prop-an", "sk-prop-kernel-lisse", "sk-prop-stalk", "sk-thm-derived-duality"]
+++
*Proposition (sketch).*

Let $S=\Spec k$ and $V=\mathbf A^r_k$. Then

$$
\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi\cong
\Delta_*\underline{E}(-r)[-2r],
\qquad
\mathcal K_\psi\ast\mathcal K_\psi\cong
(\operatorname{id}\times\iota')_*\Delta_*\underline{E}(-r)[-2r],
$$

$\Delta:V\to V\times_SV$ being the diagonal and $\iota'$ the reflection of the
addition. (Blueprint lem:fd-convolution-kernel.)

## Proof

Let $(\bar x,\bar y)$ be a geometric point of $V\times_SV$. The fibre of the
projection $r_{13}$ over $(\bar x,\bar y)$ is $\mathbf A^r_{\bar k}$, and on it
the two kernel factors restrict to $\mathcal L_{\psi(\langle\xi,x\rangle)}$ and
$\mathcal L_{\psi^{-1}(\langle\xi,y\rangle)}$; by the multiplicativity and the
inverse formula of [sk-lem-as-properties] their tensor product is
$\mathcal L_{\psi(\langle\xi,x-y\rangle)}$. So the stalk of the convolution is
$H^*_c(\mathbf A^r_{\bar k},\mathcal L_{\psi(\langle\xi,x-y\rangle)})$.
If $x\neq y$ the linear form $\xi\mapsto\langle\xi,x-y\rangle$ is nonzero: with
a linear coordinate $t=\langle\xi,c\rangle$, $c=x-y$, the sheaf is the inverse
image along a surjection $\mathbf A^r\to\mathbf A^1$ of the nonconstant
exponential sheaf. Writing $\mathbf A^r=\mathbf A^1_t\times\mathbf A^{r-1}$
with projection $\mathrm{pr}$, the projection formula and the Thom isomorphism
of [sk-prop-an] (in its compact-support form
$R\mathrm{pr}_!\underline E\cong\underline E(-(r-1))[-2(r-1)]$) give
$R\Gamma_c(\mathbf A^r_{\bar k},\mathrm{pr}^*\mathcal L_{\psi(t)})\cong R\Gamma_c(\mathbf A^1_{\bar k},\mathcal L_{\psi(t)})(-(r-1))[-2(r-1)]$, and
this vanishes: by the degreewise duality of [sk-thm-derived-duality] on the
non-proper curve $\mathbf A^1$ it is dual to the ordinary cohomology of
$\mathcal L_{\psi(-t)}(1)$, which vanishes by [sk-lem-as-properties]. If
$x=y$ the integrand is the constant sheaf, and
$R\Gamma_c(\mathbf A^r_{\bar k},\underline{E})=\underline{E}(-r)[-2r]$ by the
same Thom isomorphism. Hence the convolution is the constant sheaf with twist $(-r)$
and shift $[-2r]$ extended by zero along the diagonal, which is the first
identity; the same-character computation replaces $x-y$ by $x+y$, so the
support is the anti-diagonal, the image of the diagonal under
$\operatorname{id}\times\iota'$, giving the second.

Uses: [sk-lem-as-properties], [sk-prop-an], [sk-prop-kernel-lisse], [sk-prop-stalk], [sk-thm-derived-duality]
