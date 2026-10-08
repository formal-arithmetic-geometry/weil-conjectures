+++
id = "def-zl-frobenius-trace-series"
kind = "definition"
title = "Frobenius trace series"
order = 2388
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$, where $q=p^a$, and a prime $\ell\neq p$; write
$\Ql=\mathbf Q_\ell$ and choose an algebraic closure $\Qlb$ of $\Ql$.
A *Frobenius module* is a pair $(V,F)$ consisting of a
finite-dimensional $\Qlb$-vector space $V$ and a $\Qlb$-linear
automorphism $F:V\to V$, in the sense of the
finite-dimensional
Frobenius-module convention of the framework chapter. For such a pair, define its
*trace series* and its *determinant*

$$
\operatorname{tr}_F(T)
=\sum_{n\geq1}\Tr(F^n\mid V)\frac{T^n}{n}
\in T\Qlb[[T]],
\qquad
P_{(V,F)}(T)=\det(1-TF\mid V)\in\Qlb[T].
$$

The polynomial $P_{(V,F)}(T)$ has constant coefficient $1$ and degree
$\dim_{\Qlb}V$ (its leading coefficient is $(-1)^{\dim V}\det F\neq0$).

For a *finite graded family* of Frobenius modules
$(V_i,F_i)_{i\in I}$, indexed by a finite subset $I\subset\mathbf Z$, the
*alternating trace series* of the family is

$$
\operatorname{str}_F(T)
=\sum_{n\geq1}\left(\sum_{i\in I}(-1)^i
\Tr\bigl(F_i^n\mid V_i\bigr)\right)\frac{T^n}{n}
=\sum_{i\in I}(-1)^i\operatorname{tr}_{F_i}(T)
\in T\Qlb[[T]].
$$

No semisimplicity of $F$ (or of the $F_i$) is assumed anywhere.

In the geometric situation, let $X_0/k_0$ be
smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, put
$X=X_0\times_{k_0}k$, let $(\Qlb)_X$ be the constant
Weil sheaf, and let $F$ be the
global geometric Frobenius
on $H^i(X,\Qlb)$ in the geometric-Frobenius
convention; for every $0\leq i\leq2d$ the pair
$(H^i(X,\Qlb),F|_{H^i})$ is a Frobenius module, the trace series of the
pair being the degree-$i$ trace series obtained from the
smooth-proper
cohomological family by scalar extension. For the finite graded family
$(H^i(X,\Qlb),F|_{H^i})_{0\leq i\leq2d}$, with $I=\{0,\ldots,2d\}$, the
alternating trace series above is

$$
\operatorname{str}_F(T)
=\sum_{n\geq1}\left(\sum_{i=0}^{2d}(-1)^i
\Tr\bigl(F^n\mid H^i(X,\Qlb)\bigr)\right)\frac{T^n}{n}.
$$
