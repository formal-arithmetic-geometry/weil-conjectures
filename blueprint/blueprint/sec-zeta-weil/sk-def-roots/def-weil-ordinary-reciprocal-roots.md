+++
id = "def-weil-ordinary-reciprocal-roots"
kind = "definition"
title = "Ordinary roots and reciprocal roots"
order = 2859
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-ordinary-compact-cohomology", "def-weil-smooth-proper-cohomological-family"]
+++
Fix the finite-field datum $p$, $a\geq1$, $q=p^a$, $k_0=\Fq$, and let
$k=\Fbar$ be the fixed algebraic closure of $k_0$, and a prime $\ell\neq p$,
and choose an algebraic closure $\Qlb$ of $\Ql=\mathbf Q_\ell$. Let $X_0/k_0$
be smooth, proper, geometrically connected of pure dimension $d\in\mathbf
Z_{\geq0}$, put $X=X_0\times_{k_0}k$, fix an indeterminate $T$, and, for
every integer $i$ with $0\leq i\leq2d$, set $V_{i,\ell}=H^i(X,\Ql)$, the
ordinary cohomology group, and let $F_{i,\ell}$ be the geometric-Frobenius
[def-weil-frobenius-detailed] operator on this space, and set
$P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell})$ to be the determinant
family in the smooth-proper cohomological family
[def-weil-smooth-proper-cohomological-family]. All roots are taken in this
chosen algebraically closed field $\Qlb$.

Let $P(T)\in\Ql[T]$ be a polynomial with $P(0)=1$. An *ordinary root* is a
scalar $\beta\in\Qlb$ satisfying $P(\beta)=0$. It is nonzero. A *reciprocal
root* is a scalar $\alpha\in\Qlb^\times$ satisfying $P(\alpha^{-1})=0$. Over
an algebraic closure one has

$$
 P(T)=\prod_j(1-\alpha_jT),
$$

where the $\alpha_j$, counted with algebraic multiplicity, are the reciprocal
roots.
