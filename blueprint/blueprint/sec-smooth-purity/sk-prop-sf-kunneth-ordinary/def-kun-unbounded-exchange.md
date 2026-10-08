+++
id = "def-kun-unbounded-exchange"
kind = "definition"
title = "Unbounded derived exchange morphism"
order = 1664
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $\square=(f,f',g,g',\alpha)$ be a
cartesian square, let
$\Lambda$ be a commutative ring, and let
$K\in D(X_{\Et},\Lambda)$. The derived adjunction
$f'^{-1}\dashv Rf'_*$ extends to the unbounded derived categories by
[prop-weil-pbc-kinjective-resolutions-exist], and the
*exchange morphism* of $K$ is the mate

$$
\Ex_{\square,K}:g^{-1}Rf_*K\longrightarrow Rf'_*g'^{-1}K
$$

of the composite

$$
f'^{-1}g^{-1}Rf_*K\xrightarrow{\theta_\square}
g'^{-1}f^{-1}Rf_*K\xrightarrow{g'^{-1}\varepsilon_f}g'^{-1}K,
$$

exactly as in [def-weil-pbc-derived-exchange].
