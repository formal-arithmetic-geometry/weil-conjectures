+++
id = "prop-rational-descent"
kind = "theorem"
title = "Rational descent of the zeta series"
order = 2891
tags = ["latex:proposition"]
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-hankel-matrix", "def-weil-normalized-integral-fraction", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "prop-weil-rationality-criterion"]
+++
Fix a prime $p$, $a\in\mathbf Z_{\geq1}$, put $q=p^a$,
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Choose a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and let
$d\in\mathbf Z_{\geq0}$. Let $X_0/k_0$ be
smooth, proper, geometrically connected
of pure dimension $d$, with $X=X_0\times_{k_0}k$ and
$(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ the
smooth-proper
cohomological family.
Fix an indeterminate $T$. For $n\geq1$, put
$N_n(X_0)=\#X_0(\mathbf F_{q^n})$ and define the
point-count zeta series

$$
Z(X_0,T)=\exp\left(\sum_{n\geq1}N_n(X_0)\frac{T^n}{n}\right).
$$

Assume the closed-point product

$$
Z(X_0,T)=\prod_{x\in|X_0|}(1-T^{\deg(x)})^{-1}
$$

and the trace-to-determinant identity

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_{i,\ell}(T)^{(-1)^{i+1}}
\quad\text{in }\Ql(T).
$$

Writing
$Z(X_0,T)=\sum_{n\geq0}z_nT^n$, assume that its Hankel matrix
$\mathcal H(Z)=(z_{r+s})_{r,s\geq0}$ has finite rank, in the sense of the
Hankel-matrix definition; equivalently,
the sequence $(z_n)$ satisfies a linear recurrence over $\mathbf Q$ from
some index onward. A normalized presentation is a pair
$A,B\in\mathbf Z[T]$ satisfying

$$
Z(X_0,T)=A(T)/B(T),\qquad A(0)=B(0)=1,\qquad
\gcd(A,B)=1\text{ in }\mathbf Q[T],
$$

and this is the
normalized integral-fraction
condition. Then

$$
Z(X_0,T)\in\mathbf Q(T).
$$

## Proof

The finite-rank hypothesis on $\mathcal H(Z)=(z_{r+s})_{r,s\geq0}$ in
the sense of [def-weil-hankel-matrix] is exactly the finite-rank
hypothesis of [prop-weil-rationality-criterion] with
$K=\mathbf Q$, so the equivalence of its first two items gives
$Z(X_0,T)\in\mathbf Q(T)$, which is the assertion.
