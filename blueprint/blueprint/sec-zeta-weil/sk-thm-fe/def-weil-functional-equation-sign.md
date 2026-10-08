+++
id = "def-weil-functional-equation-sign"
kind = "definition"
title = "Normalized functional-equation sign"
order = 2921
uses = ["def-weil-determinant-constants", "def-weil-finite-field-fiber"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, and let
$q=p^a$ be the fixed prime power.
Fix $d\in\mathbf Z_{\geq0}$ and an indeterminate $T$. For each integer
$i$ with $0\leq i\leq2d$, let $P_i(T)\in\mathbf Z[T]$ satisfy
$P_i(0)=1$, put $b_i=\deg P_i$, and define the
determinant constant

$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T).
$$

Set

$$
\chi=\sum_{i=0}^{2d}(-1)^ib_i,
\qquad
\Delta=\prod_{i=0}^{2d}D_i^{(-1)^i}.
$$

Assume $d\chi$ is even; in geometric applications this follows from the
duality relations $b_i=b_{2d-i}$, $D_iD_{2d-i}=q^{db_i}$, and the
evenness of the middle degree when $d$ is odd. Define

$$
h=\frac{d\chi}{2}\in\mathbf Z
$$

and

$$
\varepsilon=
(-1)^\chi q^{-h}\Delta
\in\mathbf Q^\times.
$$

Negative exponents in $\Delta$ denote multiplicative inverses in
$\mathbf Q^\times$.
