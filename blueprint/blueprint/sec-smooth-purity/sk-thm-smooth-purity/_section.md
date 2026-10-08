+++
id = "sk-thm-smooth-purity"
kind = "section"
title = "Finite-coefficient smooth purity"
order = 2008
uses = ["sk-def-purity-conv", "sk-lem-diag-reg", "sk-prop-an", "sk-prop-cohsm", "sk-thm-dnc"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift", "AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_twistShift"]
+++
*Theorem (sketch).*

In the conventions of [sk-def-purity-conv], let $f:X\to Y$ be smooth
separated of pure relative dimension $d$. Then

$$
\omega_f=Rf^{!}\Lambda_Y\ \cong\ \Lambda_X(d)[2d],
$$

canonically; for every $K\in D^b_{ctf}(Y,\Lambda)$ the tensor formula
[sk-prop-cohsm] (b) gives the purity isomorphism

$$
Rf^{!}K\ \cong\ Lf^{*}K(d)[2d].
$$

These isomorphisms are compatible with base change and with composition
of smooth morphisms (twist additivity). *Agreement on the model:*
for the projection $\pi$ of a vector bundle of rank $d$ (in particular for
$p_d:\Aaf^d_Y\to Y$) the isomorphism $\omega_\pi\cong\Lambda(d)[2d]$
constructed below is the $R\pi^{!}$-form $\gamma_{\pi,\Lambda}$ of
[sk-prop-an] (ii) (detailed: lem:pur-projection-purity-agreement).

## Proof

Put $W=X\times_YX$, let $p_1,p_2$ be its projections and let
$\Delta:X\hookrightarrow W$ be the diagonal.
*Step 1: the section invariant of the diagonal is $\omega_f$.* The
square with $p_1,p_2$ over $f$ is Cartesian and $p_1$ is the base change of
$f$, so $\omega_{p_1}\cong Lp_2^{*}\omega_f$ by [sk-prop-cohsm] (c). Since
$p_2\circ\Delta=\mathrm{id}_X$,

$$
\mathcal C(p_1,\Delta)=L\Delta^{*}\omega_{p_1}
\cong L\Delta^{*}Lp_2^{*}\omega_f\cong\omega_f .
$$

*Step 2: the deformation to the normal cone of that section.* $\Delta$
is a closed section of the smooth map $p_1$, with normal bundle
$N_\Delta\cong T_{X/Y}$ of rank $d$ by [sk-lem-diag-reg]. Applying
[sk-thm-dnc] to $(p_1,\Delta)$ gives

$$
\mathcal C(p_1,\Delta)\ \cong\ \mathcal C(\pi_T,0_T),\qquad
\pi_T:T_{X/Y}\to X .
$$

*Step 3: the other side is the Tate twist.* Vector-bundle purity,
the $R\pi^{!}$-form [sk-prop-an] (ii) applied to $\pi_T$, gives
$\omega_{\pi_T}=R\pi_T^{!}\Lambda_X\cong\Lambda_{T_{X/Y}}(d)[2d]$, and
pulling back along the zero section,

$$
\mathcal C(\pi_T,0_T)=L0_T^{*}\omega_{\pi_T}
\cong L0_T^{*}\Lambda_{T_{X/Y}}(d)[2d]\cong\Lambda_X(d)[2d].
$$

Combining the three steps gives $\omega_f\cong\Lambda_X(d)[2d]$. Every step
is canonical, by the uniqueness clause of [sk-thm-dnc]; base-change
compatibility follows from that of the diagonal, of [sk-thm-dnc] and of
[sk-prop-an] (ii), the normal bundle of the diagonal of a base change being the
base change of the normal bundle. Substitution into [sk-prop-cohsm] (b)
gives the purity map for every $K$. Compatibility with composition is
that of [sk-prop-cohsm] (a),(c) and of the twist.

*Agreement on the model.* Let $f=\pi:E\to Z$ be a vector bundle of
rank $d$ with zero section $0_E$. Then $p_1:W=E\times_ZE\to E$ is the
bundle $\pi^{*}E$ and $\Delta$ is the translate of its zero section by the
tautological section; translation is an automorphism of $W$ over $E$
carrying $(p_1,\Delta)$ to $(\pi^{*}E,0)$, and the trace $\int_{\pi^{*}E}$,
hence $\gamma_{\pi^{*}E,\Lambda}$, is translation invariant, because the
class of every section of a vector bundle integrates to $1$ (the integral
of the class of the universal section is a locally constant function on
$E$, equal to $1$ along the zero section by [sk-prop-an] (iii), and every
connected component of $E$ meets the zero section, the fibres of $\pi$
being connected). Under $\gamma_{\pi,\Lambda}$ and $\gamma_{\pi^{*}E,\Lambda}$
the base-change isomorphism of Step 1 is the identity (base-change
compatibility in [sk-prop-an] (ii)); on the standard pair $(\pi^{*}E,0)$
the deformation space is $\pi^{*}E\times\Aaf^1$ with constant family object
([sk-lem-geometry] (4)) and the isomorphism of [sk-thm-dnc] is the
identity on the standard section invariant (its normalization clause); and
Step 3 is $L0^{*}$ of $\gamma_{\pi_T,\Lambda}$ with
$T=N_\Delta\cong\pi^{*}E$. Hence the composite of Steps 1–3 is
$\gamma_{\pi,\Lambda}^{-1}$: the isomorphism $\omega_\pi\cong\Lambda_E(d)[2d]$
of this theorem for $\pi$ is the $R\pi^{!}$-form of [sk-prop-an] (ii)
(detailed: lem:pur-projection-purity-agreement).

Uses: [sk-def-purity-conv], [sk-lem-diag-reg], [sk-prop-an], [sk-prop-cohsm], [sk-thm-dnc]
