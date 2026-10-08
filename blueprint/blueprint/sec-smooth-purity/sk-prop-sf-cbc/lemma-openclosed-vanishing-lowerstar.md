+++
id = "lemma-openclosed-vanishing-lowerstar"
kind = "lemma"
title = "$j^*i_*$ vanishes"
order = 1535
lean = ["AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range"]
+++
Let $j\colon U\to X$ and $i\colon Z\to X$ have disjoint ranges, with $j$ an
open immersion. Then $j^*i_*\mathcal H=0$ for every
$\mathcal H\in\shv{\et Z}$.

## Proof

For an open immersion $j$ the functor $j^*$ is restriction along the
base-change functor $\et X\to\et U$, so for $T\in\et U$, regarded as an
object of $\et X$ through $j$,

$$
(j^*i_*\mathcal H)(T)=(i_*\mathcal H)(T)=\mathcal H(T\times_XZ).
$$

The structure morphism $T\to X$ factors through $j$, so its range is
contained in that of $j$ and hence disjoint from that of $i$; a fibre product
of two morphisms with disjoint ranges is empty
(`AlgebraicGeometry.Scheme.isEmpty_pullback` in Mathlib: a point of
$V\times_XW$ gives a point of $X$ in both ranges), so $T\times_XZ$ is empty.
The
sheaf condition for the empty covering of the empty scheme says that
$\mathcal H(\emptyset)$ is a terminal object, and in an additive category a
terminal object is a zero object. A sheaf all of whose sections are zero is
a zero object of $\shv{\et U}$.
