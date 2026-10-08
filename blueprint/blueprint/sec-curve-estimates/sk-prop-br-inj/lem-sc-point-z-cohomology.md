+++
id = "lem-sc-point-z-cohomology"
kind = "lemma"
title = "Cohomology of the constant sheaf $\\mathbf Z$ on a point"
order = 901
+++
Let $k$ be an algebraically closed field. Then
$H^q(\operatorname{Spec}k_{\Et},\mathbf Z)=0$ for all $q\geq1$.

## Proof

The etale topos of $\operatorname{Spec}k$ is equivalent to the
category of discrete $\operatorname{Gal}(k_s/k)$-sets: a finite
etale $k$-algebra is a product of finite separable extensions of
$k$, i.e. a finite set with a continuous
$\operatorname{Gal}(k_s/k)$-action (the classical equivalence of
Galois theory), and an etale sheaf $F$ on $\operatorname{Spec}k$
corresponds to the discrete $\operatorname{Gal}(k_s/k)$-module
$F(k_s)$ (every etale cover of $\operatorname{Spec}k$ is a
disjoint union of finite etale schemes, so $F$ is determined by
the stalk $F(k_s)$ with its Galois action, and conversely every
discrete Galois module defines such a sheaf); the global sections
functor corresponds to taking $\operatorname{Gal}(k_s/k)$-invariants.
Hence $H^q(\operatorname{Spec}k_{\Et},\mathbf Z)$ is the group
cohomology $H^q(\operatorname{Gal}(k_s/k),\mathbf Z)$. For $k$
algebraically closed, $k_s=k$ and the Galois group is trivial, so
$H^q=0$ for $q\geq1$ (the group cohomology of the trivial group
with any coefficients vanishes in positive degrees: the functor of
invariants of the trivial group is exact).
