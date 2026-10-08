+++
id = "sk-def-ops"
kind = "section"
title = "The six operations, the dualizing complex, the duals"
order = 2408
uses = ["sk-def-set"]
lean = ["AlgebraicGeometry.ProEtale.dualizingComplex", "AlgebraicGeometry.ProEtale.verdierDual", "AlgebraicGeometry.ProEtale.derivedDual", "AlgebraicGeometry.ProEtale.cohomology"]
+++
*Definition (sketch).*

In the setting of [sk-def-set], let $\Dctf(X,\Lambda)$ be the bounded
constructible finite-Tor category on the small pro-étale site, with
$Lf^*,Rf_*,Rf_!,Rf^!,\otimes^L_\Lambda,R\mathcal H om_\Lambda$, where
$Rf_!$ is defined by a compactification and $Rf_!\dashv Rf^!$. Put

$$
\omega_{X,\Lambda}=Ra_X^!\Lambda,\qquad
\mathbb D_XK=\RHomX(K,\omega_{X,\Lambda}),\qquad
K^\vee=\RHomX(K,\Lambda_X),
$$

and $\RGammac(X,K)=\Fib_s(Ra_{X!}K)$,
$\RGamma(X,K)=\Fib_s(Ra_{X*}K)$, with cohomology $H^i_c,H^i$.
(Blueprint 1 and 15, def:weil-ordinary-compact-cohomology,
def:weil-exceptional-inverse-image.)

Uses: [sk-def-set]
