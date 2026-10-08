+++
id = "sk-thm-sf-dual-perfect"
kind = "section"
title = "The dual of a perfect complex"
order = 2177
uses = ["sk-def-sf-orientation", "sk-lem-sf-twist-interchange", "sk-prop-sf-dualizable-biduality"]
lean = ["AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual", "AlgebraicGeometry.Etale.Orientation.isDualizable_verdierDual"]
+++
*Theorem (sketch).*

Let $f:X\to Y$ be smooth, separated of finite type and of pure relative
dimension $d$, with orientation
$\gamma_f=\gamma_{f,\Lambda_Y}:\Lambda_X(d)[2d]\xrightarrow{\sim}Rf^!\Lambda_Y$
of [sk-def-sf-orientation] (which is [sk-thm-smooth-purity]; the base $Y$
is arbitrary within the setting of [sk-def-sf-orientation]). Put
$\mathbb D_{X/Y}K=\RHom_X(K,Rf^!\Lambda_Y)$ and let
$K\in\Dctf(X,\Lambda)$ be perfect over $\Lambda_X$. Then the composite

$$
\theta_{f,K}:\ \mathbb D_{X/Y}K=\RHom_X(K,Rf^!\Lambda_Y)
\xrightarrow{\ \RHom_X(K,\gamma_f^{-1})\ }
\RHom_X\bigl(K,\Lambda_X(d)[2d]\bigr)
\xrightarrow{\ \sim\ }K^\vee(d)[2d],
$$

whose second arrow is the canonical twist isomorphism of
[sk-lem-sf-twist-interchange] with $m=d$, $n=2d$, is an isomorphism, natural
in $K$; so $\mathbb D_{X/Y}$ restricts to an anti-equivalence on the perfect
objects, and under $\theta_f$ the biduality $K\to\mathbb D_{X/Y}\mathbb
D_{X/Y}K$ is the coefficient-dual biduality $K\to K^{\vee\vee}$ of
[sk-prop-sf-dualizable-biduality]. The absolute case is $Y=\Spec k$,
$f=a_X$: then $\mathbb D_{X/Y}=\mathbb D_X$, $Rf^!\Lambda=\omega_X$, and we
write $\gamma_X=\gamma_{a_X}$ and $\theta_K=\theta_{a_X,K}:\mathbb
D_XK\xrightarrow{\sim}K^\vee(d)[2d]$.

## Proof

The first arrow is $\RHom_X(K,-)$ of the isomorphism $\gamma_f^{-1}$, hence
an isomorphism; the second is [sk-lem-sf-twist-interchange] with $m=d$
together with the shift of the second variable, an isomorphism since $K$ is
perfect. Both are natural in $K$, and nothing about the base $Y$ beyond the
orientation is used. Applying $\theta_f$ twice and
[sk-lem-sf-twist-interchange] with $m=-d$ to the perfect $K^\vee$ gives
$\mathbb D_{X/Y}\mathbb D_{X/Y}K\cong K^{\vee\vee}$, under which the biduality is
$K\to K^{\vee\vee}$, an isomorphism by [sk-prop-sf-dualizable-biduality].

Uses: `\Cref{def-sf-orientation}`, `\Cref{lem-sf-twist-interchange}`, `\Cref{sk-prop-sf-dualizable-biduality}`
