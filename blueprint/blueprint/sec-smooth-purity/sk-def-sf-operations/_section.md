+++
id = "sk-def-sf-operations"
kind = "section"
title = "The six operations: ambient typing"
order = 1453
lean = ["AlgebraicGeometry.Etale.upperStar", "AlgebraicGeometry.Etale.rightDerivedLowerShriek", "AlgebraicGeometry.Etale.rightDerivedUpperShriek", "AlgebraicGeometry.Etale.derivedTensor", "AlgebraicGeometry.Etale.derivedHom", "AlgebraicGeometry.Etale.openImmersionLowerShriek"]
+++
*Definition (sketch).*

For a separated finite-type $f:X\to Y$ the six operations are the following
functors of ambient categories, with the framework and proper-base-change
chapters supplying the definitions:

3pt
1. **(i)** the derived pullback, the derived tensor product and the derived
internal Hom
$$
\begin{aligned}
Lf^*&:D(Y,\Lambda)\longrightarrow D(X,\Lambda),\\
-\otimes^L_\Lambda-&:D(Y,\Lambda)\times D(Y,\Lambda)\longrightarrow D(Y,\Lambda),\\
\RHom_\Lambda(-,-)&:D(Y,\Lambda)^{\mathrm{op}}\times D(Y,\Lambda)\longrightarrow D(Y,\Lambda),
\end{aligned}
$$
as in def:weil-derived-pullback-tensor-hom;
1. **(ii)** the derived direct image
$Rf_*:D^+(X,\Lambda)\to D^+(Y,\Lambda)$, as in
def:weil-derived-direct-image;
1. **(iii)** extension by zero $j_!:D^+(U,\Lambda)\to D^+(X,\Lambda)$ for an
open immersion $j:U\hookrightarrow X$, as in def:weil-extension-by-zero;
1. **(iv)** the compact-support direct image $Rf_!=R\bar f_*j_!$ attached to a
compactification $X\xrightarrow{j}\overline X\xrightarrow{p}Y$, as a functor of
ambient categories, the compactification-independence being asserted only on
the étale-origin complexes of def:compact-support-direct-image;
1. **(v)** *the ambient exceptional right adjoint* $Rf^{\times}$, an
*optional and conditional* notion that nothing downstream uses. It is
not defined, it is *assumed*: a functor of ambient categories
$$
Rf^{\times}:D(Y,\Lambda)\longrightarrow D(X,\Lambda)
$$
which is right adjoint to $Rf_!$ of (iv). Its *existence* — together
with $\operatorname{FullCD}$ for the proper part of the compactification and
the compatibility of units and counits with refinements, and with no
assertion about its values — is the *ambient exceptional right adjoint
datum*, clause (1) of [sk-def-sf-admissible]. The stronger
*admissibility datum* of [sk-def-sf-admissible] adds the two
preservation clauses (2)–(3); nothing in (v) uses them. *Warning.*
The existence hypothesis of this datum, $\operatorname{FullCD}$ on
*every* pro-étale sheaf of $A$-modules, *fails* already for the
structure morphism of an elliptic curve $E$ over $\overline{\mathbf F}_p$ with
$A=\mathbf F_r$, $r\neq p$: there is a pro-étale $A$-module sheaf
$\mathcal F$ on $E$ with $H^n(E_{\Proet},\mathcal F)\neq0$ for every
$n\ge1$, and for that morphism $Rf_!=Rf_*$ does not preserve the coproduct
$\bigoplus_n\mathcal F[n]$ and has no right adjoint on $D(E_{\Proet},A)$,
nor on $D^+$ ([sk-rem-sf-fullcd-scope]). Accordingly the datum
is never a hypothesis of a result used on the proof chain to the final
theorems [sk-thm-weil1]–[sk-thm-weil5]; $Rf^{\times}$ is kept only as
the name of the functor whose existence [sk-def-sf-admissible] (1) would
assert, in the two ambient statements [sk-lem-sf-mate] (a) and
[sk-thm-sf-package] (1);
1. **(vi)** *the exceptional inverse image* $Rf^!$, a functor of the
small categories
$$
Rf^!:\Dctf(Y,\Lambda)\longrightarrow\Dctf(X,\Lambda),
$$
*defined unconditionally* for every separated finite-type morphism
$f:X\to Y$ of finite-type $k$-schemes, as follows. At a finite stage
$\Lambda=A=A_{E,n}$ let $f^{\times}:D(Y_{\Et},A)\to D(X_{\Et},A)$ be the
right adjoint of the étale compact-support functor $Rf^{\Et}_!$, which
exists unconditionally by [sk-prop-sf-existence] (a) (Brown
representability on the ordinary étale derived categories of the Noetherian
schemes $X$, $Y$). Every object of $\Dctf(Y,A)$ is of étale origin,
$L\cong\nu_Y^*G$ with $G\in\Dctf(Y_{\Et},A)$ unique up to unique isomorphism
([09AK](https://stacks.math.columbia.edu/tag/09AK), [sk-prop-sf-comparison]), and one *defines*
$$
Rf^!L:=\nu_X^*\,f^{\times}G\;=\;\nu_X^*\,f^{\times}R\nu_{Y,*}L ,
$$
the étale right adjoint transported along the étale/pro-étale
comparison (the second formula makes sense on all of $D^+(Y_{\Proet},A)$ and
agrees with the first on $\Dctf$, since $G\to R\nu_{Y,*}\nu_Y^*G$ is an
isomorphism by the full faithfulness of $\nu_Y^*$ on $D^+$). Its two
defining properties are *theorems*, not hypotheses: the
*adjunction*
$\operatorname{Hom}_Y(Rf_!K,L)\cong\operatorname{Hom}_X(K,Rf^!L)$,
natural in every bounded-below $K$ of étale origin — in particular every
$K\in\Dctf(X,A)$ — and every bounded-below $L$, with units and counits
compatible with refinements of the compactification
([sk-prop-sf-existence] (c)); and the *preservation*
$Rf^!\Dctf(Y,A)\subseteq\Dctf(X,A)$, with explicit bounds on the
constructible interval and on the Tor amplitude
([sk-prop-sf-rf-shriek-preservation], [sk-thm-sf-ctf-stability] (v); the
primary source for the preservation of constructibility and of finite Tor
dimension with the non-regular coefficient rings $\mathcal O_E/\varpi_E^n$ is
Zheng, arXiv:1006.3810, Prop. 2.29(2), 3.16, 3.21 and Lemma 3.18). At the
adic stages $\mathcal O_E$, $E$, $\Qlb$ the functor is defined levelwise on
the normalized systems, $Rf^!(L_n)_n=(Rf^!_nL_n)_n$, the finite-reduction
isomorphisms $Rf^!_n(L_n)\otimes^L_{A_{E,n}}A_{E,m}\cong Rf^!_m(L_m)$
($m\le n$) of [sk-thm-sf-ctf-stability] (vii) making the result a normalized
system again, followed by rationalization and the common-stage construction
(def:weil-exceptional-inverse-image,
prop:coef-integral-exceptional-adjoint,
lem:coef-rational-operations). Thus in this blueprint $Rf^!$ always
denotes this constructible exceptional adjoint, and $Rf^{\times}$ the
hypothetical ambient functor of (v); when the latter exists and satisfies the
preservation clauses, its restriction to $\Dctf$ agrees with $Rf^!$ by
uniqueness of adjoints, but nothing below needs this.

The exchange and projection transformations of [sk-def-sf-exchanges] are
natural transformations between composites of these functors, and are
therefore typed by the above. Whether an operation descends to a small
category is *not* part of this definition; it is [sk-rem-sf-typing].
