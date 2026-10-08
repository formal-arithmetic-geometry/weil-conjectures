+++
id = "def-weil-betti-numbers"
kind = "definition"
title = "Betti numbers"
order = 2865
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-smooth-proper-cohomological-family"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$ and
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Let $X_0/k_0$ be
smooth, proper, and geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, and put
$X=X_0\times_{k_0}k$. Fix an indeterminate $T$. For every prime
$\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and for
$P(T)=\sum_r c_rT^r\in\mathbf Z[T]$ write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$, and let
$(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ be the
smooth-proper
cohomological family, and let $P_i(T)\in\mathbf Z[T]$ be the
integral Frobenius factor
with $P_i(0)=1$ and $P_i^{(\ell)}=P_{i,\ell}$ for every $\ell\neq p$.
For
$0\leq i\leq2d$, define

$$
b_i=\deg P_i.
$$

For every integer $i<0$ or $i>2d$, put $b_i=0$.
