+++
id = "sk-prop-stalk"
kind = "section"
title = "P3: the stalks are fibre integrals"
order = 2698
lean = ["AlgebraicGeometry.Etale.fourierTransformStalkIso"]
uses = ["sk-def-as", "sk-def-ft", "sk-def-kernel", "sk-prop-sf-cbc"]
+++
*Proposition (sketch).*

Let $S=\Spec k$, $V\cong\mathbf A^r_k$, let $\bar\xi:\Spec\Omega\to V^\vee$
be a geometric point of $V^\vee$, $\Omega$ algebraically closed, and
$K\in\Dbc(V,E)$. Write
$V_{\bar\xi}=(V\times_kV^\vee)\times_{p_2,V^\vee}\bar\xi=V\times_k\Omega$ for
the fibre of $p_2$ over $\bar\xi$: it is $V_{\bar k}$ when $\bar\xi$ is a
$\bar k$-point of $V^\vee$, and for $\bar\xi$ lying over a non-closed point
it is the affine $r$-space over $\Omega\supset\kappa(\bar\xi)$. Then

$$
\bigl(\FT_\psi(K)\bigr)_{\bar\xi}
\cong H^*_c\bigl(V_{\bar\xi},\,K|_{V_{\bar\xi}}\otimes^L\mathcal L_{\psi(\langle x,\xi\rangle)}\bigr)[r],
$$

where $\langle x,\xi\rangle:V_{\bar\xi}\to\mathbf A^{1}$ is the pairing with
the point $\xi$.
(Blueprint lem:fd-stalk-formula.)

## Proof

Form the Cartesian square with $g=\bar\xi:\Spec\Omega\to V^\vee$ and
$p_2:V\times_kV^\vee\to V^\vee$; its base change
$p_2':V_{\bar\xi}\to\Spec\Omega$ is the structure morphism of
$V_{\bar\xi}\cong\mathbf A^{r}_\Omega$, and $g':V_{\bar\xi}\to V\times_kV^\vee$
is $(\mathrm{pr}_V,\bar\xi)$. The stalk at $\bar\xi$ of a complex on
$V^\vee$ is its inverse image along $g$, so compact-support base change
([sk-prop-sf-cbc], at the $E$-stage on $\Dbc$, where $p_1^*K$ and the
kernel live) gives

$$
\bigl(Rp_{2!}(p_1^*K\otimes^L\mathcal K_\psi)\bigr)_{\bar\xi}
=Lg^*Rp_{2!}(p_1^*K\otimes^L\mathcal K_\psi)
\cong Rp'_{2!}\,Lg'^*(p_1^*K\otimes^L\mathcal K_\psi)
=R\Gamma_c\bigl(V_{\bar\xi},\,g'^*(p_1^*K\otimes^L\mathcal K_\psi)\bigr).
$$

Here $g'^*p_1^*K=K|_{V_{\bar\xi}}$, and
$g'^*\mathcal K_\psi=g'^*b^*\mathcal L_\psi$ is the Artin–Schreier sheaf of
the function $b\circ g'=\langle x,\xi\rangle$ on $V_{\bar\xi}$, because the
inverse image of $\mathcal L_{\psi,f}$ along a morphism $h$ is
$\mathcal L_{\psi,f\circ h}$ (the Artin–Schreier covering of [sk-def-as]
is compatible with base change). Taking cohomology and inserting the shift
$[r]$ of [sk-def-ft] gives the formula. The base change used is the
proper, i.e. compact-support, one along $\bar\xi\to V^\vee$; smooth base
change is not what is needed here. (If one instead passes through the
strict henselization $\Spec\mathcal O^{\mathrm{sh}}_{V^\vee,\bar\xi}$, the
kernel on $V\times_k\Spec\mathcal O^{\mathrm{sh}}_{V^\vee,\bar\xi}$ is
$\mathcal L_{\psi(\langle x,\xi_{\mathrm{univ}}\rangle)}$ for the tautological
point $\xi_{\mathrm{univ}}$, not the pullback of
$\mathcal L_{\psi(\langle x,\xi\rangle)}$ from $V_{\bar\xi}$, and the passage
to the closed fibre is again this compact-support base change.)

Uses: [sk-def-as], [sk-def-ft], [sk-def-kernel], [sk-prop-sf-cbc]
