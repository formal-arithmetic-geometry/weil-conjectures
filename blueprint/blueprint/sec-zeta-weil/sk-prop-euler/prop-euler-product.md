+++
id = "prop-euler-product"
kind = "theorem"
title = "Closed-point and integral-series identity"
order = 2877
lean = ["AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum", "AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod"]
tags = ["latex:proposition"]
uses = ["def-weil-point-counts-zeta", "lemma-nagata-affine-finite-type-is-quasi-affine"]
+++
For every finite-type $\Fq$-scheme $Y_0$ and every $n\geq1$, the
closed points of degree dividing $n$ and the geometric Frobenius orbits give

$$
\#Y_0(\mathbf F_{q^n})
=\sum_{r\mid n}r\,c_r,
$$

where $c_r$ is the number of closed points of degree $r$. Consequently

$$
Z(Y_0,T)
=\prod_{y\in|Y_0|}(1-T^{\deg(y)})^{-1}
\in1+T\mathbf Z[[T]].
$$

The product is coefficientwise locally finite: modulo $T^{m+1}$, only
closed points of degree at most $m$ occur.

**Status.** Both displayed identities are formalized and proved in Lean, over
$\mathbf Q$. The integrality assertion
$Z(Y_0,T)\in1+T\mathbf Z[[T]]$ is not part of either Lean statement.
