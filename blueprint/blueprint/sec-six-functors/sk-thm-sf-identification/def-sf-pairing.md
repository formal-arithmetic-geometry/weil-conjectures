+++
id = "def-sf-pairing"
kind = "definition"
title = "Derived Poincare pairing"
order = 2185
uses = ["def-sf-cup", "def-sf-datum", "def-sf-orientation", "def-sf-pf", "def-weil-exceptional-inverse-image"]
+++
In the setting of [def-sf-datum] and [def-sf-orientation], let
$X$ be smooth, separated of finite type and geometrically connected of pure
dimension $d$ over $k$, with structure morphism
$a_X:X\to s=\operatorname{Spec}k$ (whose exceptional inverse image is the
constructible one of [def-weil-exceptional-inverse-image]; no admissibility
hypothesis is imposed), and assume either that $X$ is
proper, or that $X=X_0\times_{k_0}k$ for a smooth, separated finite-type,
geometrically connected $k_0$-scheme $X_0$ (in the latter case no
properness is required); these are the hypotheses of global Verdier
duality. Let $K\in D^b_{ctf}(X,\Lambda)$ be such that $K^\vee$ is perfect
on $X$. The
*derived Poincare pairing* is the composite

$$
\beta_K:\ R\Gamma_c(X,K)\otimes^L_\Lambda
R\Gamma\bigl(X,K^\vee(d)\bigr)[2d]\longrightarrow\Lambda,
$$

$$
\begin{array}{lll}
R\Gamma_c(X,K)\otimes^L_\Lambda R\Gamma(X,K^\vee(d))[2d]
&\xrightarrow{\ \smile_c\ }&
R\Gamma_c\bigl(X,K\otimes^L_{\Lambda_X}K^\vee(d)\bigr)[2d]\\[2pt]
&\xrightarrow{\ R\Gamma_c(\operatorname{ev}_K(d))[2d]\ }&
R\Gamma_c\bigl(X,\Lambda_X(d)\bigr)[2d]\\[2pt]
&\xrightarrow{\ \operatorname{Tr}^{\mathrm{sm}}_{a_X,\Lambda}\ }&
\Lambda,
\end{array}
$$

where $\smile_c$ is the mixed-support cup product of
[def-sf-cup], $\operatorname{ev}_K$ is the
evaluation of [def-sf-pf], and
$\operatorname{Tr}^{\mathrm{sm}}_{a_X,\Lambda}$ is the normalized smooth
trace, i.e. the counit of $Ra_{X!}\dashv Ra_X^!$ read through the
orientation of [def-sf-orientation]. A morphism
$b:C\otimes^L_\Lambda D\to\Lambda$ of point complexes is *perfect* if
its tensor–internal-Hom adjoint $D\to C^\vee$ is an isomorphism.
