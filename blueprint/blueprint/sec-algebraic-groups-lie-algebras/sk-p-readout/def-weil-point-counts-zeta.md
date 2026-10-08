+++
id = "def-weil-point-counts-zeta"
kind = "definition"
title = "Point counts and zeta function"
order = 2553
lean = ["AlgebraicGeometry.Scheme.Hom.X_mul_derivative_zetaSeries", "AlgebraicGeometry.Scheme.Hom.degreeOver", "AlgebraicGeometry.Scheme.Hom.pointCount", "AlgebraicGeometry.Scheme.Hom.zetaSeries"]
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-scheme-morphism-properties"]
+++
Fix the finite-field datum $p,a,q,k_0,k$, where $q=p^a$, and use geometric
Frobenius [def-weil-frobenius-detailed]; let $Y_0$ be a finite-type $k_0$-scheme. Fix
an indeterminate $T$. For every integer $n\geq1$, put

$$
 Y_0(\mathbf F_{q^n})=\operatorname{Hom}_{k_0}
 (\operatorname{Spec}\mathbf F_{q^n},Y_0),
 \qquad
 N_n(Y_0)=\#Y_0(\mathbf F_{q^n}).
$$

Write $|Y_0|$ for the set of closed points of $Y_0$. For a closed point
$x\in|Y_0|$, let $\kappa(x)$ be its residue field and set
$\deg(x)=[\kappa(x):\Fq]$. For every integer $r\geq1$, put

$$
 c_r=\#\{x\in|Y_0|:\deg(x)=r\}.
$$

Define the Hasse--Weil zeta series by

$$
 Z(Y_0,T)=
 \exp\left(\sum_{n\geq1}N_n(Y_0)\frac{T^n}{n}\right)
 \in1+T\mathbf Q[[T]].
$$

The exponential is the formal power-series exponential.
