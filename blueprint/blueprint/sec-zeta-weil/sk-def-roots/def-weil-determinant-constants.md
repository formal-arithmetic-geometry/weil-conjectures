+++
id = "def-weil-determinant-constants"
kind = "definition"
title = "Determinant constants and Euler characteristic"
order = 2866
uses = ["def-weil-betti-numbers", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-smooth-proper-cohomological-family"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$; let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and fix an
indeterminate $T$. For $P(T)=\sum_r c_rT^r\in\mathbf Z[T]$, write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$ for coefficientwise extension.
Let
$X_0/k_0$ be smooth,
proper, and geometrically connected of pure dimension
$d\in\mathbf Z_{\geq0}$, and put $X=X_0\times_{k_0}k$. Let $F$ be
geometric Frobenius. For each integer $i$
with $0\leq i\leq2d$, let

$$
V_{i,\ell}=H^i(X,\Ql),\qquad
F_{i,\ell}=F\vert_{V_{i,\ell}},\qquad
P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell}).
$$

These data form the
smooth-proper
cohomological family, where $H^i(X,\Ql)$ is
ordinary cohomology. Let
$P_i(T)\in\mathbf Z[T]$ be an
integral Frobenius factor
with $P_i(0)=1$ and $P_i^{(\ell)}(T)=P_{i,\ell}(T)$, and define the
Betti number
$b_i=\deg P_i=\dim_{\Ql}V_{i,\ell}$.
For a polynomial $P(T)=\sum_{r\geq0}c_rT^r$, with coefficients
$c_r$ indexed by integers $r\geq0$, and an integer $m\geq0$, write
$[T^m]P(T)=c_m$ for its coefficient of $T^m$.
For $0\leq i\leq2d$, set

$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T)\in\mathbf Z\setminus\{0\}.
$$

The image of $D_i$ in $\Ql$ is
$\det(F_{i,\ell}\mid H^i(X,\Ql))$. Define

$$
\chi=\sum_{i=0}^{2d}(-1)^ib_i.
$$

Define also the alternating determinant scalar

$$
\Delta=\prod_{i=0}^{2d}D_i^{(-1)^i}\in\mathbf Q^\times.
$$
