+++
id = "lem-fd-convolution-kernel"
kind = "lemma"
title = "The convolution of the Fourier kernels is the delta kernel"
order = 2714
lean = ["AlgebraicGeometry.Etale.fourierKernelConvolutionIso"]
uses = ["def-pod-perfect-complex-on-x", "def-pur-conventions", "def-wf-tate-twist", "fix-prop-projection-formula", "lem-fd-as-cover-affine-line", "lem-fd-as-lisse", "lem-fd-cohomology-affine-line-character", "lem-fd-kernel-composition", "lem-fd-stalk-formula", "prop-kernel-lisse", "thm-pod-degreewise-perfectness-over-a-field", "thm-pur-vector-bundle-thom"]
+++
Let $S=\Spec k$ and $V=\mathbf A^r_k$. Then

$$
\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi\cong
\Delta_*\overline{\mathbf Q}_\ell(-r)[-2r],
\qquad
\mathcal K_\psi\ast\mathcal K_\psi\cong
(\operatorname{id}\times\iota')_*\Delta_*\overline{\mathbf Q}_\ell(-r)[-2r],
$$

where $\Delta:V\to V\times_SV$ is the diagonal and $\iota'$ is the inverse
of the addition.

## Proof

Let $(\bar x,\bar y)$ be a geometric point of $V\times_SV$. By the same
stalk computation as in [lem-fd-stalk-formula] – the fibre of $r_{13}$
over $(\bar x,\bar y)$ is $\mathbf A^r_{\bar k}$, and the kernel restricts
to the product of the two values of $\psi$ – the stalk of
$\mathcal K_{\psi^{-1}}\ast\mathcal K_\psi$ at $(\bar x,\bar y)$ is the
compactly supported cohomology

$$
H^*_c\bigl(\mathbf A^r_{\bar k},\,
\mathcal L_{\psi(\langle\xi,x\rangle)}\otimes^L
\mathcal L_{\psi^{-1}(\langle\xi,y\rangle)}\bigr)
=H^*_c\bigl(\mathbf A^r_{\bar k},\,
\mathcal L_{\psi(\langle\xi,x-y\rangle)}\bigr),
$$

the identification being the multiplicativity and the inverse formula of
[prop-kernel-lisse], [lem-fd-as-lisse]. If $x\neq y$ the linear form
$\xi\mapsto\langle\xi,x-y\rangle$ is nonzero: choose linear coordinates on
$\mathbf A^r_{\bar k}$ whose first coordinate is $t=\langle\xi,c\rangle$
with $c=x-y$, so that $\mathbf A^r_{\bar k}=\mathbf A^1_t\times\mathbf A^{r-1}$
and the sheaf is $\mathrm{pr}^*\mathcal L_{\psi(t)}$ for the projection
$\mathrm{pr}:\mathbf A^r\to\mathbf A^1_t$, a trivial vector bundle of rank
$r-1$. The vector-bundle Thom isomorphism [thm-pur-vector-bundle-thom] (in
the $\overline{\mathbf Q}_\ell$ transport of [def-pur-conventions]) gives
$R\mathrm{pr}_!\overline{\mathbf Q}_\ell\cong
\overline{\mathbf Q}_\ell(-(r-1))[-2(r-1)]$, so the projection formula
[fix-prop-projection-formula] gives

$$
R\Gamma_c\bigl(\mathbf A^r_{\bar k},\mathrm{pr}^*\mathcal L_{\psi(t)}\bigr)
\cong R\Gamma_c\bigl(\mathbf A^1_{\bar k},
\mathcal L_{\psi(t)}\otimes R\mathrm{pr}_!\overline{\mathbf Q}_\ell\bigr)
\cong R\Gamma_c\bigl(\mathbf A^1_{\bar k},\mathcal L_{\psi(t)}\bigr)
(-(r-1))[-2(r-1)].
$$

The last complex vanishes by the degreewise Poincare duality of
[thm-pod-degreewise-perfectness-over-a-field] for the smooth, separated (not
proper) curve $\mathbf A^1$ at the field stage $\overline{\mathbf Q}_\ell$,
applied to the lisse rank-one, hence perfect
([def-pod-perfect-complex-on-x]), sheaf $\mathcal L_{\psi(t)}$: it gives
$H^i_c(\mathbf A^1,\mathcal L_{\psi(t)})^\vee\cong
H^{2-i}(\mathbf A^1,\mathcal L_{\psi(t)}^\vee(1))$, and the coefficient dual
$\mathcal L_{\psi(t)}^\vee=\mathcal L_{\psi(-t)}$ ([lem-fd-as-lisse]) is the
exponential sheaf of a nonzero linear function, whose ordinary cohomology
vanishes by [lem-fd-cohomology-affine-line-character]. If $x=y$ the
integrand is the constant sheaf, and
$R\Gamma_c(\mathbf A^r_{\bar k},\overline{\mathbf Q}_\ell)
=\overline{\mathbf Q}_\ell(-r)[-2r]$, Frobenius-compatibly, by the same Thom
isomorphism [thm-pur-vector-bundle-thom] for the trivial rank-$r$ bundle over
the point. The stalk
computation therefore identifies the convolution with the constant sheaf with
twist $(-r)$ and shift $[-2r]$ extended by zero along the diagonal, which
is the first displayed isomorphism; the support is closed because the diagonal
is a closed immersion. The same-character computation replaces $x-y$ by
$x+y$, so the vanishing locus is the anti-diagonal $\{x+y=0\}$, the image
of the diagonal under $\operatorname{id}\times\iota'$, which gives the
second isomorphism.
