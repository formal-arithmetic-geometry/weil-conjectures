+++
id = "thm-weil-final-functional-equation"
kind = "theorem"
title = "Weil conjectures V: functional equation"
order = 2937
lean = ["AlgebraicGeometry.Scheme.weil_conjectures", "AlgebraicGeometry.WeilFunctionalEquation"]
uses = ["def-weil-betti-numbers", "def-weil-determinant-constants", "def-weil-finite-field-fiber", "def-weil-functional-equation-sign", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-point-counts-zeta", "prop-duality-reciprocity", "prop-functional-equation", "prop-poincare-pairing", "thm-weil-final-betti", "thm-weil-final-integrality"]
+++
Fix a finite field
$k_0=\mathbf F_q$ of characteristic $p$, with algebraic closure
$k=\overline{\mathbf F}_q$.
Let $X_0/k_0$ be
smooth, proper and geometrically
connected of pure dimension $d\geq0$, and put $X=X_0\times_{k_0}k$.
Let $P_i\in\mathbf Z[T]$, $0\leq i\leq2d$, be the
integral Frobenius factors
provided by [thm-weil-final-integrality]: $P_i(0)=1$, and for
every $\ell\neq p$,

$$
P_i^{(\ell)}(T)=\det(1-TF_{i,\ell}\mid H^i(X,\mathbf Q_\ell)),
$$

where $F_{i,\ell}$ is
geometric Frobenius
on ordinary cohomology,
and $P_i^{(\ell)}$ means coefficientwise extension
$\mathbf Z\to\mathbf Q_\ell$.
Let $Z(X_0,T)$ denote the
point-count zeta series.
If
$P(T)=\sum_{m\geq0}c_mT^m$, write
$[T^m]P(T)=c_m$. For every integer $i$ with $0\leq i\leq2d$, define the
determinant constants

$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T),
$$

with $b_i=\deg P_i$ as in [thm-weil-final-betti], and set the Euler
characteristic

$$
\chi=\sum_{i=0}^{2d}(-1)^ib_i.
$$

Then $d\chi$ is even and, for every integer $i$ with $0\leq i\leq2d$,

$$
P_{2d-i}(q^{-d}T^{-1})
=(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T),
$$

and

$$
Z(X_0,q^{-d}T^{-1})
=\varepsilon q^{d\chi/2}T^\chi Z(X_0,T)
$$

for the sign

$$
\varepsilon=
(-1)^\chi q^{-d\chi/2}
\prod_{i=0}^{2d}D_i^{(-1)^i}
\in\{1,-1\}.
$$

The sign $\varepsilon$ is the
normalized functional-equation
sign.

## Proof

Use the determinant definitions in [def-weil-determinant-constants].
The reciprocity calculation [prop-duality-reciprocity], whose duality
input is [prop-poincare-pairing], gives

$$
P_{2d-i}(q^{-d}T^{-1})
=(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T),
\qquad D_iD_{2d-i}=q^{db_i}.
$$

Pairing $i$ with $2d-i$, and using the middle-degree alternating-form
case in [prop-duality-reciprocity], shows that $d\chi$ is even. Thus
the sign is defined by [def-weil-functional-equation-sign]. Finally,
substitution into the rational factorization of the
[def-weil-point-counts-zeta] zeta series and reindexing gives exactly
the functional-equation identity in [prop-functional-equation],
with $\chi$ and $b_i$ as in [def-weil-betti-numbers].
