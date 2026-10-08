+++
id = "prop-weil-betti-comparison"
kind = "theorem"
title = "Betti-number comparison"
order = 2926
tags = ["latex:proposition"]
uses = ["def-weil-betti-numbers", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-smooth-proper-cohomological-family", "prop-cohomological-finiteness", "prop-integral-recovery"]
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
cohomological family. Let $P_i(T)\in\mathbf Z[T]$ be the
integral Frobenius factor
with $P_i(0)=1$ and $P_i^{(\ell)}=P_{i,\ell}$ for every
$\ell\neq p$, and define the Betti
numbers by $b_i=\deg P_i$ for $0\leq i\leq2d$ and $b_i=0$
otherwise. Write $H^i(X,\Ql)$ for
ordinary cohomology.
For every integer $i$ and every $\ell\neq p$,

$$
b_i=\dim_{\Ql}H^i(X,\Ql).
$$

In particular, the integers $b_i$ are independent of $\ell$, vanish
outside $0\leq i\leq2d$, and in the displayed range agree with the degrees
of the integral factors.

## Proof

For $0\leq i\leq2d$, [def-weil-betti-numbers] gives
$b_i=\deg P_i$, and [prop-integral-recovery] identifies this degree
with $\dim_{\Ql}H^i(X,\Ql)$. Outside the displayed range,
[def-weil-betti-numbers] gives $b_i=0$, while
[prop-cohomological-finiteness] gives $H^i(X,\Ql)=0$. Hence the
comparison is independent of $\ell$.
