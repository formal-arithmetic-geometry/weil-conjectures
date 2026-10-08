+++
id = "def-weil-global-geometric-frobenius"
kind = "definition"
title = "Global geometric Frobenius"
order = 2061
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-ordinary-compact-cohomology", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, a
prime $\ell\neq p$. Write $\Ql=\mathbf Q_\ell$, choose an algebraic closure
$\Qlb$ of $\Ql$, and choose a finite extension $E/\Ql$ contained in $\Qlb$.
Let $Y_0$ be a separated finite-type
[def-weil-scheme-morphism-properties] $k_0$-scheme, put
$Y=Y_0\times_{k_0}k$, set $\gamma=\operatorname{Frob}_q$, the geometric
Frobenius [def-weil-frobenius-detailed], and
$g_Y=\operatorname{id}_{Y_0}\times\operatorname{Spec}(\gamma):Y\to Y$, and
choose $(K,\theta_K)\in D^b_{c,\mathrm W}(Y,E)$. The Weil structure
[def-weil-weil-sheaf-complex] is the isomorphism formed with the derived
pullback [def-weil-derived-pullback-tensor-hom]
$Lg_Y^*\operatorname{For}(K)\xrightarrow{\sim}\operatorname{For}(K)$, and the
ordinary cohomology [def-weil-ordinary-compact-cohomology] endomorphism is
induced by

$$
 \RGamma(Y,\operatorname{For}K)\xrightarrow{\sim}
 \RGamma(Y,Lg_Y^*\operatorname{For}K)
 \xrightarrow{\RGamma(\theta_K)}\RGamma(Y,\operatorname{For}K).
$$

The compactly supported endomorphism is the explicitly defined composite

$$
\RGammac(Y,\operatorname{For}K)\xrightarrow{\sim}
\RGammac(Y,Lg_Y^*\operatorname{For}K)
 \xrightarrow{\RGammac(\theta_K)}\RGammac(Y,\operatorname{For}K),
$$

where $s=\operatorname{Spec} k$ and
$\RGammac(Y,-)=\operatorname{Fib}_s(Ra_{Y!}(-))$. Both operators, and their
actions on cohomology [def-weil-ordinary-compact-cohomology], are denoted
$F$.
