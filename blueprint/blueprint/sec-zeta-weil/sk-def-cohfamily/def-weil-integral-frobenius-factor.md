+++
id = "def-weil-integral-frobenius-factor"
kind = "definition"
title = "Integral realization of a Frobenius factor"
order = 2857
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-smooth-proper-cohomological-family"]
+++
Fix a prime $p$, $a\in\mathbf Z_{\geq1}$, put $q=p^a$,
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Let $X_0/k_0$ be
smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, with
$X=X_0\times_{k_0}k$. Fix an indeterminate $T$. For every prime
$\ell\neq p$, write
$\Ql=\mathbf Q_\ell$, and let
$P_{i,\ell}\in\Ql[T]$, $0\leq i\leq2d$, be the determinant factors in the
smooth-proper
cohomological family.
For $P(T)=\sum_{r\geq0}a_rT^r\in\mathbf Z[T]$, write

$$
P^{(\ell)}(T)=\sum_{r\geq0}(a_r\cdot1_{\Ql})T^r\in\Ql[T].
$$

For an integer $i$ with $0\leq i\leq2d$, an integral
realization-independent factor in degree
$i$ is a polynomial
$P_i\in\mathbf Z[T]$ such that

$$
P_i^{(\ell)}=P_{i,\ell}
$$

for every prime $\ell\neq p$.
