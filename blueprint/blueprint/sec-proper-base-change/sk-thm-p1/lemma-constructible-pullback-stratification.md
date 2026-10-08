+++
id = "lemma-constructible-pullback-stratification"
kind = "lemma"
title = "Pullback of a stratification"
order = 1164
lean = ["AlgebraicGeometry.Scheme.Stratification.pullback"]
uses = ["def-constructible-stratification"]
+++
Let $g\colon Y\to X$ be a morphism and let $(\iota_k\colon Z_k\to X)_{k<n}$
be a stratification of $X$. Then the base changes
$(\iota'_k\colon Z_k\times_XY\to Y)_{k<n}$ form a stratification of $Y$,
with strata $g^{-1}(X_k)$.

## Proof

Immersions are stable under base change, and the image of the base change
$Z_k\times_XY\to Y$ of $\iota_k$ is the preimage $g^{-1}(\iota_k(Z_k))$:
the underlying set of a fibre product of schemes surjects onto the
set-theoretic fibre product, so the image of the projection to $Y$ is
exactly the set of points of $Y$ whose image in $X$ lies in the image of
$\iota_k$. The sets $g^{-1}(X_k)$ are locally closed, pairwise disjoint and
cover $Y$, as preimages of the locally closed, pairwise disjoint sets $X_k$
covering $X$.
