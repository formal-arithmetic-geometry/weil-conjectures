+++
id = "thm-sf-global-duality"
kind = "theorem"
title = "Global Verdier duality"
order = 2181
uses = ["def-sf-datum", "def-sf-pf", "def-trf-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-coefficient-point", "lem-sf-point", "thm-sf-verdier-exchange"]
+++
In the setting of [def-sf-datum], let $X$ be smooth, separated of finite
type and geometrically connected of pure dimension $d$ over $k$, with
structure morphism $a_X$ (no admissibility hypothesis: $Ra_X^!$ is the
constructible exceptional inverse image of
[def-weil-exceptional-inverse-image], and $a_X$ is exceptionally admissible
in the sense of [def-trf-admissibility] as every separated finite-type
morphism is). Assume either
that $X$ is proper, or that $X=X_0\times_{k_0}k$ for a smooth, separated
finite-type, geometrically connected $k_0$-scheme $X_0$; in the latter
case no properness is required. Let $K\in D^b_{ctf}(X,\Lambda)$. Then
there is a canonical isomorphism

$$
R\Gamma_c(X,K)^\vee\xrightarrow{\ \sim\ }R\Gamma\bigl(X,\mathbb D_XK\bigr)
$$

in the point category $D^b_c(s,\Lambda)$ of
[def-weil-finite-coefficient-point], natural in $K\in D^b_{ctf}(X,\Lambda)$
and compatible with finite reduction, scalar extension, and shifts. For
$K=\Lambda_X$ it specializes to
$R\Gamma_c(X,\Lambda)^\vee\cong R\Gamma(X,\omega_X)$.

## Proof

Apply [thm-sf-verdier-exchange] with $Y=s$, $f=a_X$ and $M=K$:
$D_s(Ra_{X!}K)\cong Ra_{X*}D_XK$. Apply $\Fib_s$ and the point
identifications of [lem-sf-point]: the left-hand side becomes
$R\operatorname{Hom}_\Lambda(R\Gamma_c(X,K),\Lambda)=R\Gamma_c(X,K)^\vee$
and the right-hand side becomes
$\Fib_s(Ra_{X*}D_XK)=R\Gamma(X,\mathbb D_XK)$. Since $\Fib_s$ is an
equivalence onto the point category by [lem-sf-point], the resulting
composite is an isomorphism in $D^b_c(s,\Lambda)$, and it is the displayed
isomorphism; naturality and the compatibilities are those of
the two ingredients. The argument uses only the exceptional adjunction for $a_X$ (so that
[thm-sf-verdier-exchange] applies to $f=a_X$, $Y=s$), which is available
for every separated finite-type morphism, never that $a_X$ is proper: the compact-support image
$Ra_{X!}$ and the ordinary image $Ra_{X*}$ enter as two different
functors, and no comparison $Ra_{X!}\cong Ra_{X*}$ is invoked. Hence the
same proof covers both cases of the hypothesis, the proper one and the
nonproper one $X=X_0\times_{k_0}k$. The constant case is
$\mathbb D_X\Lambda_X=R\mathcal H om_X(\Lambda_X,Ra_X^!\Lambda)=\omega_X$
by [def-sf-pf].
