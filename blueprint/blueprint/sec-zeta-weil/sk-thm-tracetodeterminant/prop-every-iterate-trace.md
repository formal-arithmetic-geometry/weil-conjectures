+++
id = "prop-every-iterate-trace"
kind = "theorem"
title = "Every-iterate Grothendieck–Lefschetz identity"
order = 2881
tags = ["latex:proposition"]
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-local-frobenius-trace", "def-weil-ordinary-compact-cohomology", "def-weil-point-counts-zeta", "def-weil-scheme-morphism-properties", "def-weil-smooth-proper-cohomological-family", "def-weil-weil-sheaf-complex", "prop-cohomological-finiteness", "thm-weil-grothendieck-lefschetz-trace"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$. Choose a prime $\ell\neq p$, write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and
choose a finite extension $E/\Ql$ contained in $\Qlb$, and a
separated finite-type
$k_0$-scheme $Y_0$, and
$Y=Y_0\times_{k_0}k$. Let
$K\in D^b_{c,\mathrm W}(Y,E)$ be a
Weil complex, let
$F$ be its global
geometric-Frobenius action on
compactly supported
cohomology. For every
integer $n\geq1$ and each point $x\in Y_0(\mathbf F_{q^n})$, choose a
geometric point
$\bar x\to Y$ over $x$. The local operators
$F_x^{(n)}$ and the stalk complexes
$K_{\bar x}=L\bar x^*\operatorname{For}(K)$, using the
derived pullback; these are the
local Frobenius and stalk
constructions; their alternating traces are independent of the choices.
The sets $Y_0(\mathbf F_{q^n})$ and their cardinalities $N_n(Y_0)$ use the
point-count convention.
For every such $n$, one has

$$
\sum_{x\in Y_0(\mathbf F_{q^n})}\sum_{j\in\mathbf Z}(-1)^j
\Tr\bigl(F_x^{(n)}\mid
\mathcal H^j(\operatorname{For}K)_{\bar x}\bigr)
=\sum_{i\in\mathbf Z}(-1)^i
\Tr\bigl(F^n\mid H_c^i(Y,K)\bigr).
$$

Both sums are finite. For the constant
Weil sheaf $E_Y$, each local
alternating trace is $1$, so

$$
N_n(Y_0)=\sum_{i\in\mathbf Z}(-1)^i
\Tr\bigl(F^n\mid H_c^i(Y,E)\bigr).
$$

If $Y_0$ is proper,
compactly supported
cohomology may be replaced by
ordinary cohomology. In
particular, let $X_0/\Fq$ be
smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, put
$X=X_0\times_{\Fq}k$, let $(\Ql)_X$ be its constant
Weil sheaf, and let $F_X$ be the
global geometric Frobenius
on $H^i(X,\Ql)$ for every $i\in\mathbf Z$. Put
$V_{i,\ell}=H^i(X,\Ql)$, $F_{i,\ell}=F_X|_{V_{i,\ell}}$, using the
smooth-proper
cohomological family. Then

$$
N_n(X_0)=\sum_{i=0}^{2d}(-1)^i
\Tr(F_{i,\ell}^n\mid V_{i,\ell}).
$$

## Proof

The local alternating trace is the one defined in
[def-weil-local-frobenius-trace].
The trace identity and its constant-sheaf and proper-specialization clauses
are supplied by [thm-weil-grothendieck-lefschetz-trace]; finiteness and
the Frobenius action are [prop-cohomological-finiteness]. Thus the
displayed formulae follow.
