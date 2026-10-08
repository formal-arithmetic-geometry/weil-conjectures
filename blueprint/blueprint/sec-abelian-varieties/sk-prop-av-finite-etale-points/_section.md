+++
id = "sk-prop-av-finite-etale-points"
kind = "section"
title = "Points of finite étale group schemes"
lean = ["AlgebraicGeometry.card_points_eq_finrankΓ", "AlgebraicGeometry.bijective_toUnit_comp"]
order = 579
uses = ["sk-def-av-group-scheme"]
+++
*Proposition (sketch).*

Let $G$ be a finite étale group scheme of order $m$ over an
algebraically closed field $k$, and $k\subseteq k'$ an extension of
algebraically closed fields. Then

$$
\lvert G(k)\rvert=m,\qquad G(k)\xrightarrow{\ \sim\ }G(k').
$$

## Proof

A finite étale $k$-algebra is a product of finite separable field
extensions of $k$; as $k$ is algebraically closed, each of them is
$k$. Hence $G\cong\coprod_{i=1}^m\Spec k$ as a $k$-scheme, so $G(k)$
has $m$ elements and $G(k)\to G(k')$ is a bijection.

Uses: [sk-def-av-group-scheme]
