+++
id = "thm-sc-affine-cohomology"
kind = "theorem"
title = "Kummer computation on an affine curve"
order = 1021
uses = ["def-sc-curves", "def-sc-kummer-sequence", "def-sc-mu-trivialization", "lem-sc-affine-cohomological-dimension", "lem-sc-affine-unit-quotient", "lem-sc-brauer-zero", "lem-sc-h1-gm-pic", "lem-sc-pic-affine", "lem-sc-primitive-root"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth affine connected curve over $k$, and let
$n\geq1$ be prime to $\operatorname{char}k$. Then, under the
canonical trivialization $\theta_\zeta$ of
[def-sc-mu-trivialization],

$$
H^0(C_{\Et},\mathbf F_n)\cong\mathbf Z/n\mathbf Z,\qquad
\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}
\text{ is finite},
$$

and there is a canonical short exact sequence

$$
0\longrightarrow\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}
\longrightarrow H^1(C_{\Et},\mathbf F_n)\longrightarrow
\operatorname{Pic}(C)[n]\longrightarrow0
$$

($\operatorname{Pic}(C)[n]$ finite, by [lem-sc-pic-affine]; the
unit term vanishes when $\mathcal O_C(C)^\times$ is $n$-divisible,
e.g. when $C=\mathbf A^1$), and
$H^q(C_{\Et},\mathbf F_n)=0$ for all $q>1$.

## Proof

The
[def-sc-kummer-sequence] together with
$\operatorname{Pic}(C)=H^1(C,\mathbf G_m)$
([lem-sc-h1-gm-pic]) and the vanishing
$H^2(C,\mathbf G_m)=0$ of [lem-sc-brauer-zero] (affine case)
give the long exact sequence

$$
0\to\mu_n(k)\to\mathcal O_C(C)^\times\xrightarrow{\ n\ }
\mathcal O_C(C)^\times\to H^1(C,\mu_n)\to
\operatorname{Pic}(C)\xrightarrow{\ n\ }\operatorname{Pic}(C)\to
H^2(C,\mu_n)\to 0,
$$

whence the displayed exact sequence for $H^1(C,\mu_n)$, with
$H^1(C,\mu_n)$ an extension of $\operatorname{Pic}(C)[n]$ by
$\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}$; the
$H^2$-cokernel vanishes because $\operatorname{Pic}(C)$ is
$n$-divisible ([lem-sc-pic-affine]). The $H^0$-term is
$\mu_n(k)=\mathbf Z/n\mathbf Z$ by
[lem-sc-primitive-root]; for $q>2$ the vanishing is
[lem-sc-affine-cohomological-dimension]. The finiteness of the
unit quotient is [lem-sc-affine-unit-quotient].
