+++
id = "def-weil-parity-products"
kind = "definition"
title = "Odd and even parity products"
order = 2899
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-smooth-proper-cohomological-family"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, put $q=p^a$,
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix an indeterminate $T$.
Let $X_0/k_0$ be
smooth, proper, geometrically
connected of pure dimension
$d\in\mathbf Z_{\geq0}$, with $X=X_0\times_{k_0}k$. For every prime
$\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and let
$P_{i,\ell}\in\Ql[T]$ for
$0\leq i\leq2d$ be the determinant factors in the
smooth-proper
cohomological family. Define

$$
N_\ell(T)=\prod_{\substack{0\leq i\leq2d\\ i\text{ odd}}}P_{i,\ell}(T),
\qquad
D_\ell(T)=\prod_{\substack{0\leq i\leq2d\\ i\text{ even}}}P_{i,\ell}(T).
$$
