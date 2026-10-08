+++
id = "sk-thm-picard-hilb-curves"
kind = "section"
title = "Hilbert schemes of smooth projective curves"
order = 783
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.hilbertPresheaf_curve_representable", "AlgebraicGeometry.hilbertPresheaf_curve_points", "AlgebraicGeometry.hilbertPresheaf_curve_add"]
+++
*Theorem (sketch).*

Let $X$ be a geometrically irreducible smooth proper curve over $k$
and $d\ge0$. Then:

1. **(1)** $\Hilb^d_{X/k}$ is representable by a smooth proper
*variety* of dimension $d$;
1. **(2)** for $k'/k$, the $k'$-points of $\underline{\Hilb}^d_{X/k}$
are naturally the effective Cartier divisors of degree $d$ on
$X_{k'}$;
1. **(3)** there is an addition morphism
$\underline{\Hilb}^{d_1}_{X/k}\times_k\underline{\Hilb}^{d_2}_{X/k} \to\underline{\Hilb}^{d_1+d_2}_{X/k}$, finite locally free of degree
$\binom{d_1+d_2}{d_1}$, and a universal effective Cartier divisor
$D_{\mathrm{univ}}\subseteq\underline{\Hilb}^d_{X/k}\times_kX$ with
$\cO(D_{\mathrm{univ}})|_{\{[D]\}\times X}\cong\cO_X(D)$.

## Proof

*Hypothesis check (with the seam $S_1$).* A finite set of
points of $X$ lies in an affine open: take $D_0=\sum_j[P_j]$ with
$m=\sum_j[\kappa(P_j):k]\ge1$; by [sk-thm-picard-rr] (G) (applicable:
$X$ is geometrically irreducible and smooth, hence geometrically
integral, so $H^0(X,\cO_X)=k$) the module
$\cO_X(D_0)$ is ample, and by [sk-thm-picard-rr] (H) the complement of
$\operatorname{Supp}(D_0)$ is affine and contains the points.
*Smoothness.* $\Hilb^0_{X/k}=\Spec k$ and
$\Hilb^1_{X/k}\cong X$ (degree-$1$ closed subschemes are graphs of
sections); the addition morphism $H_d\times_kX\to H_{d+1}$ is finite
locally free of degree $d+1$, hence faithfully flat, so smoothness
descends along faithfully flat morphisms — induction on $d$ giving
$\Hilb^d$ smooth of dimension $d$.
*Properness, integrality.* The iterated addition
$\pi_d:X^d\to H_d$ is finite locally free of degree $d!$ and
surjective (over $\bar k$ a finite flat scheme of rank $d$ is a sum
of closed points), hence $H_d=\pi_d(X^d)$ is proper and irreducible;
with smoothness, a variety of dimension $d$.
*Points (seam $S_2$ at work).* By the Cartier criterion
($X_T\to T$ smooth of relative dimension $1$: finite locally free
$\iff$ relative effective Cartier), the points are the effective
Cartier divisors of degree $d$. *Universal divisor*: the
universal closed subscheme is a relative effective Cartier divisor
by the same criterion; the fibre of its module is $\cO_X(D)$.
