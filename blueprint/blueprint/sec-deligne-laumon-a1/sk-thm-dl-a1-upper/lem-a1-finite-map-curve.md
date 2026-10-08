+++
id = "lem-a1-finite-map-curve"
kind = "lemma"
title = "Finite map to the affine line"
order = 2795
uses = ["def-sc-curves", "def-sc-genus", "def-weil-pbc-scheme-conventions", "lem-sc-compactification", "lem-sc-point-cartier", "lem-sc-riemann-roch", "lem-weil-pbc-finite-pullback-identities", "thm-pqf-finite-iff-proper-finite-fibres"]
+++
Let $C_0$ be a smooth affine curve which is geometrically a connected
curve. There is a smooth curve $C'_0$, geometrically a connected curve, containing $C_0$ as a
dense open with finite complement, and a finite generically etale
morphism $g:C'_0\to\mathbf A^1_{k_0}$.

## Proof

Take the smooth projective completion $\overline C$ of
[lem-sc-compactification], and choose a closed point
$s\in\overline C\setminus C_0$. Such a point exists because a
positive-dimensional proper curve is not affine.
It is an effective Cartier divisor by [lem-sc-point-cartier];
write $d_s=[\kappa(s):k_0]$, without assuming $d_s=1$.
Choose an integer $m$ prime to the characteristic and large enough
that $(m-1)d_s>2g(\overline C)-2$.
Riemann–Roch, [lem-sc-riemann-roch], gives

$$
h^0(\overline C,\mathcal O(ms))-
h^0(\overline C,\mathcal O((m-1)s))=d_s>0.
$$

Choose a function $f$ in the difference. It has its only pole at
$s$, of order exactly $m$.
The sections $1,f$ of $\mathcal O(ms)$ have no common zero:
away from $s$ the first generates, and at $s$ the second generates
because its pole has exactly the allowed order.
They define $h:\overline C\to\mathbf P^1$ with
$h^{-1}(\infty)=\{s\}$.
This map is proper and has finite fibres, so it is finite by
[thm-pqf-finite-iff-proper-finite-fibres].

It is also generically etale. Over the perfect field $k_0$, the
kernel of the differential on the one-variable function field is
$k_0(\overline C)^p$ in characteristic $p$.
A $p$-th power has valuation divisible by $p$ at every point,
whereas $\operatorname{ord}_s(f)=-m$ is not divisible by $p$.
Thus $df\neq0$, which makes the finite function-field extension
$k_0(\overline C)/k_0(f)$ separable.
Set $C'_0=\overline C\setminus\{s\}$.
The restriction $g:C'_0\to\mathbf A^1$ is finite by the base-change
stability in [lem-weil-pbc-finite-pullback-identities],
and it remains generically etale.
Since $s$ lies outside $C_0$, this $C'_0$ contains $C_0$
with finite complement.
