+++
id = "lem-zl-relative-envelope-factor-reality"
kind = "theorem"
title = "Reality of relative factors for an envelope"
order = 2841
tags = ["latex:proposition"]
uses = ["cor-trf-point-counting", "def-weil-pbc-qbar-category", "def-weil-punctual-weights", "def-wf-iota-real", "lem-a1-affine-hc0", "lem-zl-affine-curve-hc2-purity", "lem-zl-affine-curve-range", "lem-zl-euler-product-identity", "lem-zl-real-reduced-factors", "lem-zl-relative-curve-punctual", "lem-zl-root-radius-separation", "thm-cbc-qbar"]
+++
Let $h:U_0\to Y_0$ be as in [lem-zl-relative-curve-punctual], and
let $\mathcal E$ be lisse, $\iota$-real, and punctually $\iota$-pure
of weight zero. Then every $R^ih_!\mathcal E$ is $\iota$-real.

## Proof

Fix a closed point $y$ of the base. By [thm-cbc-qbar], the
local polynomials of $R^ih_!\mathcal E$ at $y$ are the polynomials
$P_i$ of the compactly supported cohomology of the fiber
$U_{\bar y}$ (the local Frobenius eigenvalues of the stalk). The
group in degree zero vanishes by (the affine-line form of) the
$H_c^0$-vanishing of lisse sheaves on nonproper curves,
[lem-a1-affine-hc0]; the roots of $P_1$ have modulus
at most $q_y^{1/2}$ by [lem-zl-relative-curve-punctual] (weight
zero, $i=1$), while every nonzero root of $P_2$ has modulus $q_y$
by the top-factor purity [lem-zl-affine-curve-hc2-purity].

The trace formula [cor-trf-point-counting] identifies the fiber
$L$-function, i.e. the exponential of the point-count series of the
fiber with coefficients $\mathcal E$, with
$P_1(T)/P_2(T)$ (the cohomological factorization over the finite
field $\kappa(y)$, with $H_c^0=0$): exponentiating the alternating
trace sum degree by degree, the Euler-product identity
[lem-zl-euler-product-identity] turns the exponential of the trace
series of $F$ on $H_c^i$ into $P_i(T)^{-1}$. Its Euler factors have real
coefficients by the $\iota$-reality of $\mathcal E$
([def-wf-iota-real] applied to the restriction to the fiber), so
this quotient lies in $\mathbf R(T)$. The radii are disjoint
($|z|\leq q_y^{1/2}$ for $P_1$, $|z|=q_y$ for the roots of
$P_2$), and [lem-zl-root-radius-separation] therefore makes the
fraction reduced with denominator $P_2$ in the reduced form; now
[lem-zl-real-reduced-factors] gives
$P_1,P_2\in\mathbf R[T]$. This holds for every $y$; degree zero is
trivial ($P_0=1$ by the vanishing), and all other degrees vanish or
are captured by [lem-zl-affine-curve-range]. This proves the
asserted $\iota$-reality.
