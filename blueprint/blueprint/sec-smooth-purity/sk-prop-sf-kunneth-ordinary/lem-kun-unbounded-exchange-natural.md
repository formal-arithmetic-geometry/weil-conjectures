+++
id = "lem-kun-unbounded-exchange-natural"
kind = "lemma"
title = "Naturality of the unbounded exchange morphism"
order = 1665
uses = ["def-kun-unbounded-exchange", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $\square=(f,f',g,g',\alpha)$ be a cartesian square and $\Lambda$
a commutative ring. For every morphism $\varphi:K\to K'$ in
$D(X_{\Et},\Lambda)$ the square

$$
\begin{array}{ccc}
g^{-1}Rf_*K&\xrightarrow{\ \Ex_{\square,K}\ }&Rf'_*g'^{-1}K\\
\Big\downarrow{\scriptstyle g^{-1}Rf_*(\varphi)}&&
\Big\downarrow{\scriptstyle Rf'_*g'^{-1}(\varphi)}\\
g^{-1}Rf_*K'&\xrightarrow{\ \Ex_{\square,K'}\ }&Rf'_*g'^{-1}K'
\end{array}
$$

commutes; that is, $K\mapsto\Ex_{\square,K}$ is natural in $K$.

## Proof

Choose a morphism of K-injective resolutions over $\varphi$, which
exists and is unique up to chain homotopy because K-injective
resolutions exist and any two of them are chain-homotopy equivalent
([prop-weil-pbc-kinjective-resolutions-exist]), and represent the
derived functors by these K-injective resolutions,
[def-weil-pbc-kinjective-resolutions].
The composite $f'^{-1}g^{-1}Rf_*K\to g'^{-1}K$ whose mate defines
$\Ex_{\square,K}$ in [def-kun-unbounded-exchange] is natural in
$K$, its constituents $\theta_\square$ and
$g'^{-1}\varepsilon_f$ being natural transformations; the mate of a
natural composite under the fixed adjunction $f'^{-1}\dashv Rf'_*$
is natural, so the displayed square commutes.
