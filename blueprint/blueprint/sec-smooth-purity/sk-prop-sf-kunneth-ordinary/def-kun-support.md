+++
id = "def-kun-support"
kind = "definition"
title = "Closed points, transcendence degree, support"
order = 1673
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-geometric-stalks", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a scheme of finite type over a field $K$ (the
scheme conventions of
the proper-base-change chapter; in particular $X$ is Noetherian, quasi-compact and
quasi-separated). A point $x\in X$ is *closed* if $\{x\}$ is
closed in $|X|$; write

$$
\operatorname{trdeg}_K\kappa(x)
$$

for the transcendence degree of the residue field $\kappa(x)$ over
$K$, and for $a\ge0$ set

$$
E_a(X)=\{x\in X:\operatorname{trdeg}_K\kappa(x)\le a\}.
$$

For an etale sheaf $F\in\Ab(X_{\Et})$, the *support*
$\kunsupp F$ is the set of $x\in X$ such that $F_{\bar x}\ne0$
for some geometric point
$\bar x$ over $x$; that this set does not depend on the choice of
the geometric point over $x$ is recorded with the other properties of
this notion. For
$K\in D(X_{\Et})$ put

$$
\kunsupp K=\bigcup_q\kunsupp\mathcal H^q(K)
$$

using the cohomology
sheaves of $K$.
