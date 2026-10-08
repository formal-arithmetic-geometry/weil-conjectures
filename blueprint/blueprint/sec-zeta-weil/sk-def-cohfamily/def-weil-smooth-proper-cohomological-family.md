+++
id = "def-weil-smooth-proper-cohomological-family"
kind = "definition"
title = "The smooth-proper cohomological family"
order = 2856
uses = ["def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-ordinary-compact-cohomology", "def-weil-weil-sheaf-complex", "prop-cohomological-finiteness"]
+++
Fix the finite-field datum $p,a,q,k_0,k$, where $q=p^a$. Let $X_0/k_0$ be
smooth, proper, geometrically connected of pure dimension $d\in\mathbf
Z_{\geq0}$, and put $X=X_0\times_{k_0}k$. For every prime $\ell\neq p$, write
$\Ql=\mathbf Q_\ell$, and let $K_{X,\ell}=(\Ql)_X$ be the constant Weil
sheaf, and let $F_\ell$ be the global geometric Frobenius on
$\RGamma(X,K_{X,\ell})$, using the geometric-Frobenius convention
[def-weil-frobenius-detailed]. Fix an indeterminate $T$. For every integer $i$ with
$0\leq i\leq2d$, define

$$
 V_{i,\ell}=H^i(X,\Ql),
\qquad
 F_{i,\ell}=F_\ell\vert_{V_{i,\ell}}.
$$

The finiteness of the spaces $V_{i,\ell}$, the invertibility of the operators
$F_{i,\ell}$, and the vanishing of $H^i(X,\Ql)$ outside $0\leq i\leq2d$ are
the cohomological-finiteness proposition, and are not part of the definition
of the family. Define

$$
 P_{i,\ell}(T)=
 \det(1-TF_{i,\ell}\mid V_{i,\ell})\in\Ql[T].
$$

It has constant coefficient $1$, degree $\dim_{\Ql}V_{i,\ell}$, and leading
coefficient $(-1)^{\dim V_{i,\ell}}\det(F_{i,\ell})$.
