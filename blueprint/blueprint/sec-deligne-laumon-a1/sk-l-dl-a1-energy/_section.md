+++
id = "sk-l-dl-a1-energy"
kind = "section"
title = "Weight detection by trace energy"
order = 2756
uses = ["sk-d-dl-a1-setup", "sk-l-dl-a1-endpoints", "sk-p-linear-spectra", "sk-prop-logdet", "sk-thm-trace-transport"]
lean = ["AlgebraicGeometry.WeilSheaf.traceEnergy", "AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le"]
+++
*Lemma (sketch).*

Let $N\ne0$ be pure of weight $v$ and lisse on a smooth geometrically
connected affine curve $V_0$. Put

$$
S_n(V_0,N)=\sum_{x\in V_0(\mathbf F_{q^n})}
|\iota\Tr(\DLAFr_x\mid N_{\bar x})|^2,
$$

where $\DLAFr_x$ means Frobenius relative to $\mathbf F_{q^n}$.
If $S_n(V_0,N)\le Cq^{nB}$ for every $n\ge1$, with $C$ independent of
$n$, then $v\le B-1$.

## Proof

Let $T_v$ be the constant Weil line whose Frobenius has realization
$q^v$, and set $N^c=N^\vee\otimes T_v$. The line $T_v$ has weight
$2v$, while $N^c$ has weight $v$ and conjugate realized local spectra.
Thus $D=N\otimes N^c$ has weight $2v$ and point traces
$|\iota t_{N,n}(x)|^2$. The trace formula and the determinant identity give

$$
E_N(T):=\exp\left(\sum_{n\ge1}S_n(V_0,N)\frac{T^n}{n}\right)
=\frac{\iota\det(1-T\DLAFr_q\mid H_c^1(V,D))}
{\iota\det(1-T\DLAFr_q\mid H_c^2(V,D))}.
$$

There is a closed point with a nonzero stalk. Some positive power of its
invertible Frobenius has nonzero trace; otherwise the determinant
identity would make its characteristic polynomial constant. Hence some
$S_n$ is positive. All $S_n$ are nonnegative, so the exponential has
infinitely many nonzero coefficients: a positive coefficient in its
exponent contributes positively in arbitrarily high powers.
Consequently the rational function $E_N$ is not a polynomial and has
at least one surviving finite pole.

By [sk-l-dl-a1-endpoints], $H_c^2(V,D)$ is pure of weight $2v+2$,
so every possible denominator pole has modulus $q^{-(v+1)}$.
The assumed energy bound makes the series in the exponential converge
for $|T|<q^{-B}$. Its analytic exponential is holomorphic there and
agrees with the rational germ; therefore the surviving pole cannot lie
in that disk. Thus $q^{-(v+1)}\ge q^{-B}$, or $v\le B-1$.
This argument uses no weight estimate for $H_c^1(V,D)$ and requires
only one surviving pole, rather than noncancellation of every factor.

Uses: [sk-d-dl-a1-setup], [sk-l-dl-a1-endpoints], [sk-prop-logdet], [sk-thm-trace-transport]
