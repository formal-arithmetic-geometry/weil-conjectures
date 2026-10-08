+++
id = "lem-wf-zariski-closure-subgroup"
kind = "lemma"
title = "Zariski closure of a matrix subgroup"
order = 2500
+++
Let $\Gamma$ be a subgroup of $\operatorname{GL}(V)$ over
$\overline{\mathbf Q}_\ell$, and let $H$ be its Zariski closure
inside $\operatorname{GL}(V)$. Then $H$ is a closed algebraic
subgroup.

## Proof

Let $f$ be a regular function on $\operatorname{GL}(V)$ vanishing
on $\Gamma$. The function $F(g,h)=f(gh)$ is regular on
$\operatorname{GL}(V)\times\operatorname{GL}(V)$. For fixed
$h\in\Gamma$, the function $g\mapsto F(g,h)$ vanishes on
$\Gamma$, since $\Gamma$ is a subgroup, and hence vanishes on $H$
by the definition of Zariski closure. Now fix $g\in H$; the function
$h\mapsto F(g,h)$ vanishes on $\Gamma$, so it vanishes on $H$.
Thus $f(gh)=0$ for all $g,h\in H$, and $HH\subseteq H$.
Likewise $g\mapsto f(g^{-1})$ is regular, vanishes on $\Gamma$,
and therefore vanishes on $H$; hence $H^{-1}\subseteq H$.
The identity belongs to $H$, so $H$ is a subgroup.
