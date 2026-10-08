+++
id = "lem-sc-finite-etale-points"
kind = "lemma"
title = "Points of finite etale group schemes"
lean = ["AlgebraicGeometry.card_points_eq_finrankΓ", "AlgebraicGeometry.bijective_toUnit_comp"]
order = 586
uses = ["def-sc-group-scheme", "lem-sc-finite-etale-algebra-criterion"]
+++
Let $G$ be a finite etale group
scheme of order $m$ over an algebraically closed field $k$, and
$k'\supseteq k$ an extension of algebraically closed fields. Then

$$
|G(k)|=m,\qquad G(k)\xrightarrow{\ \sim\ }G(k').
$$

## Proof

By [lem-sc-finite-etale-algebra-criterion], the coordinate ring
$\Gamma(G,\mathcal O_G)$ of the finite etale $G$ is a finite product of
finite separable field extensions of $k$; since $k$ is algebraically
closed each of these extensions equals $k$. Hence
$G\cong\coprod_{i=1}^{m}\operatorname{Spec}k$ as a $k$-scheme; the
order of $G$ is the $k$-dimension of its coordinate ring
([def-sc-group-scheme] fixes the group scheme structure of $G$,
and $m$ is the order of [def-sc-group-scheme] as in the
statement of the lemma), so the disjoint union has $m$ terms. Thus
$G(k)$ is a set of $m$ points and the canonical map
$G(k)\to G(k')$ is a bijection.
