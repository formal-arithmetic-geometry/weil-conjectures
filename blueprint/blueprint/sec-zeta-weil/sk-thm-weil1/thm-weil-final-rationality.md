+++
id = "thm-weil-final-rationality"
kind = "theorem"
title = "Weil conjectures I: rationality and Euler product"
order = 2928
lean = ["AlgebraicGeometry.Scheme.zetaSeries_rational"]
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-point-counts-zeta", "prop-euler-product", "prop-every-iterate-trace", "prop-rational-descent", "prop-trace-determinant", "prop-weil-rationality-criterion"]
+++
Fix a finite field
$k_0=\mathbf F_q$ of characteristic $p$, with algebraic closure
$k=\overline{\mathbf F}_q$.
Let $X_0/k_0$ be
smooth, proper and geometrically
connected of pure dimension $d\geq0$, and put $X=X_0\times_{k_0}k$.
For an indeterminate $T$, use the
point-count zeta series

$$
Z(X_0,T)=\exp\left(\sum_{n\geq1}
\#X_0(\mathbf F_{q^n})\frac{T^n}{n}\right).
$$

Here $|X_0|$ is the set of closed points and
$\deg(x)=[\kappa(x):k_0]$. Then

$$
Z(X_0,T)\in1+T\mathbf Z[[T]]\cap\mathbf Q(T),
\qquad
Z(X_0,T)=\prod_{x\in|X_0|}(1-T^{\deg(x)})^{-1}.
$$

## Proof

The exponential definition and the closed-point product are
[def-weil-point-counts-zeta], [prop-euler-product]. The trace calculation
[prop-every-iterate-trace], together with the determinant identity
[prop-trace-determinant], gives a factorization over $\Ql(T)$. By
[prop-weil-rationality-criterion], this rational expression gives finite Hankel
rank over $\Ql$; every finite Hankel minor has integral entries, so the
same rank bound holds over $\mathbf Q$. Thus the finite-rank hypothesis of
[prop-rational-descent] is verified, and its rationality statement
descends the factorization to $\mathbf Q(T)$; the integrality of the
point-count coefficients is the exponential definition above, so the two
asserted forms hold.
