+++
id = "lemma-openclosed-stalk-upperstar"
kind = "lemma"
title = "Stalks of a pullback"
order = 1109
lean = ["AlgebraicGeometry.Etale.upperStarCompSheafFiberIso", "AlgebraicGeometry.Etale.upperStarCompUliftSheafFiberIso"]
uses = ["def-kun-separably-closed", "lemma-openclosed-point-ulift"]
+++
Let $f\colon Y\to X$ be a morphism of schemes, let $\bar y$ be a geometric
point of $Y$ and let $\mathcal F\in\shv{\et X}$. Then

$$
(f^*\mathcal F)_{\bar y}\cong\mathcal F_{f\circ\bar y},
$$

naturally in $\mathcal F$.

## Proof

The functor $f^*$ is the pullback of sheaves along the morphism of sites
given by base change $\et X\to\et Y$, $V\mapsto V\times_XY$. Pulling a point
of $\et Y$ back along a morphism of sites gives a point of $\et X$, and the
stalk of a pulled-back sheaf at a point is by construction the stalk of the
sheaf at the transported point. It remains to identify the transport of the
geometric point $\bar y$ along base change with the geometric point
$f\circ\bar y$ of $X$. This is the universal property of the fibre product:
for $V\in\et X$, lifting $\bar y$ to $V\times_XY$ is the same as lifting
$f\circ\bar y$ to $V$, so the two points have the same étale neighbourhoods
and hence the same stalk functor.
