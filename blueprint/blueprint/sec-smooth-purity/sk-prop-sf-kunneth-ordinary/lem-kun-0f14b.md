+++
id = "lem-kun-0f14b"
kind = "lemma"
title = "Kunneth formula, one proper factor, $\\kunZn$-coefficients"
order = 1764
uses = ["def-kun-kunneth-map", "def-kun-separably-closed", "def-weil-pbc-scheme-conventions", "lem-kun-0f0c", "lem-kun-0f0g", "lem-kun-0f10", "lem-kun-0f12", "lem-kun-0f14a", "lem-kun-cd-sep-closed-point", "lem-kun-kunneth-map-agrees", "lem-kun-leray-unbdd", "lem-kun-proper-stability", "lem-kun-pullback-constant", "lem-kun-tensor-sym", "lem-kun-tensor-unit"]
+++
Let $k$ be a separably closed
field and let $n\ge1$ be an integer invertible in $k$. Let $X$
be a proper scheme over
$k$ and let $Y$ be a scheme of finite type over $k$. For
$E\in D(X_{\Et},\kunZn)$ and $K\in D(Y_{\Et},\kunZn)$ the Kunneth
map

$$
\kappa_{E,K}:
\RGamma(X_{\Et},E)\kunotimes{\kunZn}\RGamma(Y_{\Et},K)
\longrightarrow
\RGamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr)
$$

is an isomorphism. (*Source:* Stacks Project, Tag
[0F14](https://stacks.math.columbia.edu/tag/0F14), part (2).)

## Proof

The proof is exactly parallel to the proof of
[lem-kun-0f14a]: by [lem-kun-proper-stability] the morphism
$\operatorname{pr}_2$ is proper, and the projection formula of
[lem-kun-0f0g] (with the torsion ring
$\Lambda=\kunZn$) gives

$$
R\operatorname{pr}_{2,*}
\bigl(\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr)
\cong
R\operatorname{pr}_{2,*}\pr_1^{-1}E\kunotimes{\kunZn}K .
$$

Proper base change in the unbounded form of
[lem-kun-0f0c] yields
$R\operatorname{pr}_{2,*}\pr_1^{-1}E\cong \underline{\RGamma(X_{\Et},E)}$, the pullback of a constant object
being constant ([lem-kun-pullback-constant],
[lem-kun-tensor-unit]). Since $Y$ is of finite type over the
separably closed field $k$, [lem-kun-cd-sep-closed-point] and
[lem-kun-0f10](2) give $\kuncd(Y)<\infty$; since moreover
$\operatorname{pr}_2$ is a morphism of finite type schemes over
$k$, [lem-kun-0f10](1) gives $\kuncd(\operatorname{pr}_2)< \infty$, so [lem-kun-leray-unbdd] applies and

$$
\RGamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr)
\cong
\RGamma\bigl(Y_{\Et},
\underline{\RGamma(X_{\Et},E)}\kunotimes{\kunZn}K\bigr) .
$$

By [lem-kun-0f12] (with the constant complex
$\underline{\RGamma(X_{\Et},E)}\in D(\kunZn)$) and
[lem-kun-tensor-sym] we get an isomorphism $\theta$ to
$\RGamma(X_{\Et},E)\kunotimes{\kunZn}\RGamma(Y_{\Et},K)$, and
[lem-kun-kunneth-map-agrees](b) shows
$\theta\circ\kappa_{E,K}=\mathrm{id}$. Hence $\kappa_{E,K}$ (the
Kunneth map of [def-kun-kunneth-map]) is an isomorphism.
