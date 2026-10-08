+++
id = "sk-prop-smooth-proper-purity"
kind = "section"
title = "Smooth-proper purity"
order = 2867
lean = ["TraceDatum.isPureOfWeight_map_P_of_pairing"]
uses = ["sk-d-dl-general-weights", "sk-d-real-weights", "sk-def-cohfamily", "sk-def-sf-operations", "sk-prop-sf-comp-proper", "sk-thm-dl-general-sheaf", "sk-thm-poincare-duality", "sk-thm-properbasechange", "sk-thm-purity-transport", "sk-thm-sf-dual-perfect", "sk-thm-sf-tensor-hom", "sk-thm-smooth-base-change", "sk-thm-smooth-purity"]
+++
*Proposition (sketch).*

Let $f_0:X_0\to Y_0$ be a smooth proper morphism of separated finite-type
$k_0$-schemes of pure relative dimension $d$ (no admissibility hypothesis on
$f_0$ or the structure morphisms: the exceptional adjoints are the
unconditional ones of [sk-def-sf-operations](vi)), and let $\mathcal F_0$ be a lisse
Weil sheaf on $X_0$ which is punctually $\iota$-pure of weight $w$ in the
sense of [sk-d-real-weights]. Then for every $i$:

1. **(a)** the canonical map
$R^{i}f_{0!}\mathcal F_0\to R^{i}f_{0*}\mathcal F_0$ is an isomorphism and
this sheaf is lisse;
1. **(b)** it is punctually $\iota$-pure of weight $w+i$.

In the absolute case $Y_0=\Spec k_0$, $\mathcal F_0=(\Ql)_{X_0}$ — the
setting of [sk-def-cohfamily] — clause (b) says that every
eigenvalue $\alpha$ of geometric Frobenius on $H^{i}(X,\Ql)$ satisfies
$|\iota(\alpha)|=q^{i/2}$; there the duality step is
[sk-thm-poincare-duality] (5) and no relative duality is needed.

## Proof

The upper bound is [sk-thm-dl-general-sheaf]; the content here is that
duality supplies the matching lower bound.

*Step 1 (coincidence and local constancy).* Properness makes
$Rf_{0!}\to Rf_{0*}$ an isomorphism ([sk-prop-sf-comp-proper]), which is
the first half of (a). By [sk-thm-properbasechange] the geometric stalk
of $R^{i}f_{0*}\mathcal F_0$ at $\bar y$ is $H^{i}(X_{\bar y},\mathcal F)$,
and smoothness of $f_0$ makes these stalks locally constant in $\bar y$ by
[sk-thm-smooth-base-change]. Hence $R^{i}f_{0*}\mathcal F_0$ is lisse,
proving (a).

*Step 2 (upper bound).* A punctually pure sheaf is mixed of weights at
most $w$ in the sense of [sk-d-dl-general-weights], so
[sk-thm-dl-general-sheaf] applied to $f_0$ with $r=i$ gives weights at most
$w+i$ on $R^{i}f_{0!}\mathcal F_0=R^{i}f_{0*}\mathcal F_0$. By Step 1 this
sheaf is lisse, so the bound is punctual.

*Step 3 (lower bound by relative duality).* The base $Y_0$ may be
singular, so the duality is assembled over $Y_0$ from the tensor–Hom
exchange and the relative dual, not from the absolute Verdier duality with
$\omega_{Y}$. Write $f=f_0\times_{k_0}k$, $\mathcal F$ for the pullback of
$\mathcal F_0$ to $X$ and $\Lambda$ for the coefficient field. The
tensor–Hom form of the exchange ([sk-thm-sf-tensor-hom]) with
$M=\mathcal F$ and $N=\Lambda_Y$, together with $Rf_!=Rf_*$ from Step 1,
gives

$$
\RHom_Y\bigl(Rf_*\mathcal F,\Lambda_Y\bigr)
\;\cong\;Rf_*\RHom_X\bigl(\mathcal F,Rf^!\Lambda_Y\bigr).
$$

The smooth orientation $\Lambda_X(d)[2d]\cong Rf^!\Lambda_Y$ of
[sk-thm-smooth-purity], at the $\Qlb$-stage by
[sk-thm-purity-transport], and the relative perfect form
$\theta_{f,\mathcal F}$ of [sk-thm-sf-dual-perfect] (the lisse
$\mathcal F$ is perfect) identify the inner term:
$\RHom_X(\mathcal F,Rf^!\Lambda_Y)\cong\mathcal F^{\vee}(d)[2d]$. Hence

$$
\RHom_Y\bigl(Rf_*\mathcal F,\Lambda_Y\bigr)
\;\cong\;Rf_*\bigl(\mathcal F^{\vee}\bigr)(d)[2d].
$$

Now take cohomology sheaves in degree $-i$. On the right this is
$R^{2d-i}f_*(\mathcal F^{\vee})(d)$. On the left, every $R^{j}f_*\mathcal F$
is lisse by Step 1, hence locally free of finite rank over $\Lambda_Y$, so
$\RHom_Y(R^{j}f_*\mathcal F,\Lambda_Y)=(R^{j}f_*\mathcal F)^{\vee}$ sits in
degree $0$ (the local $\mathcal Ext^{p}$ vanish for $p>0$); the spectral
sequence $\mathcal Ext^{p}_Y(R^{-q}f_*\mathcal F,\Lambda_Y)\Rightarrow
\mathcal H^{p+q}\RHom_Y(Rf_*\mathcal F,\Lambda_Y)$ therefore degenerates and
gives $\mathcal H^{-i}\RHom_Y(Rf_*\mathcal F,\Lambda_Y)=(R^{i}f_*\mathcal F)^{\vee}$. The three isomorphisms are compatible with the Frobenius
structures, the orientation being compatible with base change, so the
outcome is a Frobenius-equivariant isomorphism of lisse sheaves

$$
\bigl(R^{i}f_{0*}\mathcal F_0\bigr)^{\vee}
\;\cong\;
R^{2d-i}f_{0*}\bigl(\mathcal F_0^{\vee}\bigr)(d).
$$

The dual $\mathcal F_0^{\vee}$ is lisse and punctually $\iota$-pure of weight
$-w$, since inverting the local eigenvalues negates the weights of
[sk-d-real-weights]. Step 2 in degree $2d-i$ bounds the weights of
$R^{2d-i}f_{0*}(\mathcal F_0^{\vee})$ by $-w+(2d-i)$, and the twist $(d)$
lowers weights by $2d$, so the right-hand side has weights at most

$$
-w+(2d-i)-2d=-w-i.
$$

Dualizing reverses weights, so $R^{i}f_{0*}\mathcal F_0$ has weights at least
$w+i$. With Step 2 this is purity of weight $w+i$, proving (b).

*Step 4 (the absolute case).* For $Y_0=\Spec k_0$ and
$\mathcal F_0=(\Ql)_{X_0}$, Step 3 may be replaced by the absolute duality
proved in this document. By Step 2, $|\iota(\alpha)|\le q^{i/2}$ for every
eigenvalue $\alpha$ of $F$ on $H^{i}(X,\Ql)$. By
[sk-thm-poincare-duality] (5) the eigenvalues of $F$ on
$H^{2d-i}(X,\Ql)\cong H^{i}(X,\Ql)^{\vee}(-d)$ are exactly the
$q^{d}/\alpha$, with multiplicity. Step 2 in degree $2d-i$ therefore gives

$$
\frac{q^{d}}{|\iota(\alpha)|}=\bigl|\iota(q^{d}/\alpha)\bigr|
\le q^{(2d-i)/2},
\qquad\text{that is}\qquad |\iota(\alpha)|\ge q^{i/2}.
$$

The two bounds give $|\iota(\alpha)|=q^{i/2}$.

*What the upgrade costs.* Steps 3 and 4 use only smoothness,
properness and duality; no no-cancellation or coprimality argument enters,
because purity is read off eigenvalue by eigenvalue. All the arithmetic
sits in [sk-thm-dl-general-sheaf]: without it Step 3 bounds nothing, and
with it both inequalities are automatic.

Uses: [sk-d-dl-general-weights], [sk-d-real-weights], [sk-def-cohfamily], [sk-prop-sf-comp-proper], [sk-thm-dl-general-sheaf], [sk-thm-poincare-duality], [sk-thm-properbasechange], [sk-thm-purity-transport], [sk-thm-sf-dual-perfect], [sk-thm-sf-tensor-hom], [sk-thm-smooth-base-change], [sk-thm-smooth-purity]
