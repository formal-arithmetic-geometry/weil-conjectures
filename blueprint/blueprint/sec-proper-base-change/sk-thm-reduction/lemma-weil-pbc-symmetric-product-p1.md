+++
id = "lemma-weil-pbc-symmetric-product-p1"
kind = "lemma"
title = "Symmetric product map"
order = 1196
uses = ["cor-pqf-proper-quasifinite-finite", "lemma-weil-pbc-cancellation", "lemma-weil-pbc-composition", "prop-weil-pbc-finite-morphism"]
+++
For $n\geq1$ the formula

$$
((x_1:y_1),\ldots,(x_n:y_n))\longmapsto
[F_0:\cdots:F_n],\qquad
\prod_{i=1}^n(x_it+y_i)=\sum_{j=0}^nF_jt^j,
$$

defines a finite surjective $S_n$-invariant morphism
$\sigma_n:(\mathbf P^1_S)^n\to\mathbf P^n_S$.

## Proof

Each $F_j$ is the sum of monomials choosing $j$ of the $x_i$ and the
remaining $y_i$; hence it is homogeneous of degree one in every pair
$(x_i,y_i)$. On the chart $y_1\cdots y_n\ne0$, the ratios
$z_i=x_i/y_i$ give elementary symmetric polynomials, so the map is induced
by the universal polynomial $\prod(T-z_i)$. On a general chart, the same
calculation uses the coefficient ring localized at one nonzero $F_j$; the
coefficients generate the unit ideal because if all $F_j$ vanished then the
homogeneous polynomial $\prod_i(x_it+y_i)$ would be zero, forcing one factor
to be $(0,0)$, impossible in projective coordinates. The coordinate ring is
integral over the symmetric subring: each $z_i$ satisfies the monic equation
$T^n-e_1T^{n-1}+\cdots+(-1)^ne_n$, and the analogous statement holds on all
charts after clearing the chosen $y_i$ or $x_i$. Thus $\sigma_n$ is finite.
Permutation of the factors leaves every $F_j$ unchanged, proving
$S_n$-invariance. To make finiteness independent of the abbreviated chart
calculation, let $[a_0:\cdots:a_n]$ be a geometric point of $\mathbf P^n_S$.
Its fibre is the set of ordered $n$-tuples of points of $\mathbf P^1$ whose
linear forms multiply to $\sum a_jt^j$. Over an algebraically closed field,
the factorization theorem for one-variable polynomials, applied after choosing
the first nonzero coefficient to decide whether $t=\infty$ is a root, gives
only finitely many such tuples (at most $n!$ after the multiplicities are
fixed). Hence $\sigma_n$ is quasi-finite.

The source $(\mathbf P^1_S)^n$ is projective over $S$, so $\sigma_n$ is
proper. On an affine target chart, the quasi-finite proper map is covered by
finitely many affine opens on which the coordinate rings are integral over the
target ring: on the chart where the last coefficient is invertible use the
monic equations for the $z_i$, and on the chart where the first coefficient
is invertible use the reversed monic equations for $w_i=y_i/x_i$; on an
intermediate chart, intersect these two covers with the finitely many opens
where a selected coefficient of the binary form is invertible. The same
monic equations after multiplying by that selected coefficient show that each
coordinate is integral. Integral algebras glue on overlaps because the
coordinate identifications are induced by the common coefficients $F_j$.
Thus the proper quasi-finite morphism is finite ([cor-pqf-proper-quasifinite-finite]). Finally a geometric binary
form of degree $n$ factors into $n$ linear forms, including the possible
factor $x$ for $t=\infty$, so every geometric fibre is nonempty; geometric
surjectivity and properness give surjectivity. This closes the chart and
gluing obligation.
