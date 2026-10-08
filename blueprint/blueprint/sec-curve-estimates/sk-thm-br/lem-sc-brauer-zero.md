+++
id = "lem-sc-brauer-zero"
kind = "lemma"
title = "The Brauer group of a smooth curve"
order = 925
uses = ["def-br", "def-sc-curves", "lem-sc-affine-open-proper", "lem-sc-brauer-injectivity", "lem-sc-compactification", "lem-sc-dim0-finite", "lem-sc-divisor-exact-sequence", "lem-sc-point-z-cohomology", "lem-sc-proper-affine-finite", "lem-sc-tsen"]
+++
Let $C$ be a smooth separated connected curve over
algebraically closed $k$. Then its Brauer group ([def-br]) vanishes:

$$
H^2(C_{\Et},\mathbf G_m)=0.
$$

## Proof

By [lem-sc-compactification] and [lem-sc-affine-open-proper],
a smooth separated connected curve is either proper or affine, and we treat
the two cases. The same vanishing, for the same class of curves, is
Stacks Project, Theorem 59.68.5,
[Tag 03RM](https://stacks.math.columbia.edu/tag/03RM); the
argument below is the independent one of this chapter.

*Proper case.* Let $\eta=\operatorname{Spec}k(C)\to C$ be
the generic point. By [lem-sc-brauer-injectivity],

$$
H^2(C_{\Et},\mathbf G_m)\hookrightarrow\operatorname{Br}(k(C)),
$$

and the target is zero by [lem-sc-tsen].

*Affine case.* Let $\overline C$ be the compactification of
[lem-sc-compactification] and
$S:=\overline C\setminus C\neq\emptyset$ the finite complement
([lem-sc-dim0-finite]; nonempty because a proper affine curve
is finite, [lem-sc-proper-affine-finite]). The divisor exact
sequence ([lem-sc-divisor-exact-sequence])

$$
0\to\mathbf G_m\to j_*\mathbf G_m\to\bigoplus_{P\in S}i_{P*}\mathbf Z\to0
$$

on $\overline C_{\Et}$ gives, since
$H^q(C_{\Et},\mathbf G_m)=H^q(\overline C_{\Et},j_*\mathbf G_m)$,
the long exact sequence

$$
\cdots\to H^1(\overline C,\textstyle\bigoplus_Pi_{P*}\mathbf Z)
\to H^2(\overline C,\mathbf G_m)
\to H^2(C,\mathbf G_m)
\to H^2(\overline C,\textstyle\bigoplus_Pi_{P*}\mathbf Z)\to\cdots.
$$

Here $H^q(\overline C,i_{P*}\mathbf Z)=H^q(\operatorname{Spec}k,\mathbf Z)=0$ for $q\geq1$: for a closed immersion $i$, the pushforward
$i_*$ is exact – on stalks, $(i_*F)_{\bar x}$ equals
$F_{\bar x}$ if $\bar x$ lies over a point of the closed
subscheme and is $0$ otherwise – and $i^*i_*F\cong F$, so
$R\Gamma(\overline C,i_*F)=R\Gamma(\{P\},F)$ and
$H^q(\overline C,i_*F)=H^q(\{P\},F)$,
by [lem-sc-point-z-cohomology], and
$H^2(\overline C,\mathbf G_m)=0$ by the proper case. Hence
$H^2(C,\mathbf G_m)=0$.
