+++
id = "sk-prop-sf-biduality-general"
kind = "section"
title = "General Verdier biduality"
order = 2113
uses = ["sk-def-sf-operations", "sk-prop-sf-rf-shriek-preservation"]
lean = ["AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual", "AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual"]
+++
*Proposition (sketch).*

Let $Y$ be a separated finite-type $k$-scheme and let $\Lambda$ be a
coefficient stage; let $Ra_Y^!$ be the constructible exceptional adjoint of
the structure morphism ([sk-def-sf-operations](vi); no admissibility datum
is assumed, cf.\ [sk-def-sf-admissible]). Then
$\mathbb D_Y=\RHom_\Lambda(-,\omega_{Y,\Lambda})$
with $\omega_{Y,\Lambda}=Ra_Y^!\Lambda\in\Dctf(Y,\Lambda)$
([sk-prop-sf-rf-shriek-preservation]) is a contravariant exact
anti-equivalence of $\Dctf(Y,\Lambda)$ with $\mathbb D_Y\mathbb D_Y\cong \mathrm{id}$: the double-dual morphism $\delta_K$ is an isomorphism for every
$K$.
Chapter 1 (framework chapter), prop:functor-package(7), restated
as thm:sf-biduality of `10b_six_functor_formalism.tex`, after
Deligne, *SGA $4\frac12$*, Ch. 5 (Dualité) 1.1–1.2 and Ch. 7
(Théorèmes de finitude) 4.1–4.6: locality, a finite smooth
stratification, the locally-free case on a stratum, and the restriction to a
stratum; the algebraic half of the coefficient hypothesis is coefficient
biduality at a geometric point, which holds stage by stage for different
reasons: at the finite stages $A_{E,n}$ (Artinian and self-injective, hence
quasi-Frobenius) finite modules are reflexive; at the integral stage
$\mathcal O_E$ is *not* quasi-Frobenius — for
$M=\mathcal O_E/(\varpi_E)$ one has $\operatorname{Hom}(M,\mathcal O_E)=0$,
so $M^{**}=0\neq M$ although $M$ is perfect — and one uses instead derived
duality of perfect complexes, $\RHom_{\mathcal O_E}(M,\mathcal O_E)\simeq M[-1]$ and $\RHom(\RHom(M,\mathcal O_E),\mathcal O_E)\simeq M$, the
$\operatorname{Ext}^1$ term being essential
([0656](https://stacks.math.columbia.edu/tag/0656),
[07VI](https://stacks.math.columbia.edu/tag/07VI): every bounded complex with
finite cohomology over the regular ring $\mathcal O_E$ is perfect, and derived
evaluation is an isomorphism for every perfect complex); at the field stages
$E$, $\Qlb$ it is vector-space duality (lem-weil-coefficient-frobenius,
rem-weil-biduality-coefficients). The Artinian-stage argument is therefore in
scope only at $A_{E,n}$; the derived-complete integral stage and the field
stages are reached from it by the coefficient transports
thm-coef-integral-verdier, thm-coef-rational-verdier, thm-coef-qbar-verdier.
nothing: the former hypothesis "$a_Y$ carries the ambient datum" (the
hypothesis of [sk-prop-sf-existence] (b), false in general by
[sk-rem-sf-fullcd-scope]) has been discharged, the dualizing
complex being formed with the unconditional constructible adjoint of
[sk-def-sf-operations] (vi) and [sk-prop-sf-existence] (c); the detailed
proof thm:fix-general-biduality is a geometric argument on $\Dctf$ that
uses no ambient adjoint.
Uses: `prop-functor-package`, `thm-sf-biduality-class`
