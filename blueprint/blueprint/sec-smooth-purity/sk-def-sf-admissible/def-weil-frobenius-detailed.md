+++
id = "def-weil-frobenius-detailed"
kind = "definition"
title = "Arithmetic and geometric Frobenius"
order = 1504
uses = ["def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
For the global finite-field datum [def-weil-finite-field-fiber], the
arithmetic Frobenius of $k$ is

$$
 \varphi_q:k\longrightarrow k,
 \qquad z\longmapsto z^q.
$$

Put $\gamma=\operatorname{Frob}_q=\varphi_q^{-1}$. For a finite-type
[def-weil-scheme-morphism-properties] $k_0$-scheme $Y_0$, set
$Y=Y_0\times_{k_0}k$ and define the associated semilinear automorphism

$$
 g_Y=\operatorname{id}_{Y_0}\times\Spec(\gamma):Y\longrightarrow Y.
$$

This is distinct from the absolute $q$-power morphism of $Y$; every Frobenius
operator in this blueprint is induced by $g_Y$ and is geometric.
