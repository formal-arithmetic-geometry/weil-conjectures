+++
id = "sk-p-real-rankin"
kind = "section"
title = "Rankin–Selberg upper bound"
order = 2657
uses = ["sk-d-real-cohom", "sk-d-real-detweights", "sk-d-real-operations", "sk-d-real-series", "sk-d-real-setup", "sk-d-real-weights", "sk-d-real-weil", "sk-p-linear-filtration", "sk-p-linear-spectra", "sk-p-linear-triangular", "sk-p-real-operations", "sk-p-real-rankone", "sk-p-tensor", "sk-thm-derived-duality", "sk-thm-trace-transport"]
lean = ["AlgebraicGeometry.WeilGroup.hasWeightsAtMost_of_isReal"]
+++
*Proposition (sketch).*

Let $U_0$ be an affine smooth geometrically connected
curve over $\Fq$, and let $\mathcal F\ne0$ be a
$\iota$-real lisse Weil sheaf.
If $d$ is the largest determinant weight of
its irreducible constituents, all its local Frobenius eigenvalues
have $\iota$-weight at most $d$.

## Proof

For $m\ge1$, put $\mathcal H_m=\mathcal F^{\otimes2m}$.
The tensor rule in [sk-p-tensor] bounds its constituent determinant
weights by $2md$. By [sk-thm-derived-duality], [sk-d-real-operations],
$H_c^2(U,\mathcal H_m)= (\mathcal H_{m,\bar\eta})_{\pi_1(U)}(-1)$.
On the untwisted quotient only one Frobenius operator remains.
Triangularize it by [sk-p-linear-triangular]. Its one-dimensional successive
quotients $B_b$ are also constituents of $\mathcal H_m$, so
[sk-d-real-detweights] gives $|\iota b|\le q^{md}$.
Thus top-cohomology eigenvalues have modulus at most $q^{md+1}$.
Using $H_c^0=0$, [sk-thm-trace-transport] and [sk-d-real-cohom],
together with the elementary fact that a Cauchy product preserves a common
lower bound on radii, yields

$$
R\bigl(L_\iota(U_0,\mathcal H_m,T)\bigr)
\ge R_m=q^{-md-1}.
$$

For any matrix $A$, triangularization and the formal geometric series give

$$
\det(1-TA)^{-1}
=\exp\left(\sum_{n\ge1}\Tr(A^n)\frac{T^n}{n}\right).
$$

In the local factor for $\mathcal H_m$, the trace inside the exponential
is $(\iota\Tr(F_x^n\mid\mathcal F_{\bar x}))^{2m}\ge0$, since
$\mathcal F$ is real in [sk-d-real-weights].
Consequently all inverse local factors have nonnegative coefficients.
For a locally finite product of such series with constant terms $1$,
each coefficient of an individual factor is bounded by the corresponding
coefficient of the product. By the radius definition in [sk-d-real-series],
each factor therefore has radius at least $R_m$.

If $\alpha$ is a local eigenvalue and $e=e_x$, then
$\alpha^{2m}$ occurs on $\mathcal H_m$ by [sk-p-linear-spectra].
Its local denominator has a root of modulus
$|\iota\alpha|^{-2m/e}$; since $B(0)=1$ and $R(B^{-1})\ge R_m$ force every
zero of $B$ to have modulus at least $R_m$ (a zero cannot cancel the
numerator $1$), this gives

$$
|\iota\alpha|^{-2m/e}\ge q^{-md-1},\qquad
\wt_{\iota,q_x}(\alpha)\le d+\frac1m .
$$

Letting $m\to\infty$ proves the desired bound.

Uses: [sk-d-real-cohom], [sk-d-real-detweights], [sk-d-real-operations], [sk-d-real-series], [sk-d-real-setup], [sk-d-real-weights], [sk-d-real-weil], [sk-p-linear-spectra], [sk-p-linear-triangular], [sk-p-real-rankone], [sk-p-tensor], [sk-thm-derived-duality], [sk-thm-trace-transport]
