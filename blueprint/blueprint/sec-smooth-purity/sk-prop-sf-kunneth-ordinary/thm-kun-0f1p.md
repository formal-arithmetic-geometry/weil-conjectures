+++
id = "thm-kun-0f1p"
kind = "theorem"
title = "Kunneth formula, etale cohomology"
order = 1781
uses = ["def-kun-kunneth-map", "def-kun-separably-closed", "lem-kun-0f10", "lem-kun-0f12", "lem-kun-0f1n", "lem-kun-cd-sep-closed-point", "lem-kun-kunneth-via-0f1n", "lem-kun-leray-unbdd"]
+++
Let $k$ be a separably closed
field and let $X$ and $Y$ be schemes of finite type over $k$.
Let $n\ge1$ be an integer invertible in $k$. Then for
$E\in D(X_{\Et},\kunZn)$ and $K\in D(Y_{\Et},\kunZn)$ the
Kunneth map of [def-kun-kunneth-map]

$$
\kappa_{E,K}:\RGamma(X_{\Et},E)\kunotimes{\kunZn}\RGamma(Y_{\Et},K)
\longrightarrow
\RGamma\bigl((X\times_kY)_{\Et},
\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr)
$$

is an isomorphism. (*Source:* Stacks Project, Tag
[0F1P](https://stacks.math.columbia.edu/tag/0F1P).)

## Proof

By [lem-kun-0f1n] applied to the diagram

$$
\begin{array}{ccccc}
X&\xleftarrow{\;=\;}&X&\xleftarrow{\;\pr_1\;}&X\times_kY\\
\Big\downarrow{}&&\Big\downarrow{}&&\Big\downarrow{\scriptstyle \pr_2}\\
\Spec(k)&\longleftarrow&\Spec(k)&\xleftarrow{\;=\;}&Y
\end{array}
$$

(all schemes of finite type over $k$, $n$ invertible in $k$) we
have the isomorphism

$$
\varphi:
E\kunotimes{\kunZn}\underline{\RGamma(Y_{\Et},K)}
\longrightarrow
R\pr_{1,*}\bigl(\pr_1^{-1}E\kunotimes{\kunZn}\pr_2^{-1}K\bigr).
$$

We conclude by [lem-kun-kunneth-via-0f1n] and the following
two identifications: first,
$\RGamma((X\times_kY)_{\Et},-)\cong\RGamma(X_{\Et},-)\circ R\pr_{1,*}$
by [lem-kun-leray-unbdd], which applies because $\pr_1$ is a
qcqs morphism of finite type schemes over $k$ and
$\kuncd(\pr_1)<\infty$ by [lem-kun-0f10](1); second,

$$
\RGamma\bigl(X_{\Et},E\kunotimes{\kunZn}\underline{\RGamma(Y_{\Et},K)}\bigr)
\cong\RGamma(X_{\Et},E)\kunotimes{\kunZn}\RGamma(Y_{\Et},K)
$$

by [lem-kun-0f12], which applies because
$\kuncd(X)<\infty$ by [lem-kun-cd-sep-closed-point] and
[lem-kun-0f10](2). Hence $\kappa_{E,K}$ (the Kunneth map of
[def-kun-kunneth-map]) is an isomorphism, as desired.
