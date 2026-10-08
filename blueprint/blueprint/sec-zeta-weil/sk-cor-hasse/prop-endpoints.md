+++
id = "prop-endpoints"
kind = "theorem"
title = "Endpoint cohomology and endpoint factors"
order = 2914
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-weil-betti-numbers", "def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-smooth-proper-cohomological-family", "prop-cohomological-finiteness", "prop-integral-recovery", "prop-poincare-pairing"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and fix an
indeterminate $T$. For $P(T)=\sum_r c_rT^r\in\mathbf Z[T]$, write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$ for coefficientwise extension.
Let
$X_0/k_0$ be smooth, proper,
geometrically connected of pure dimension $d\in\mathbf Z_{\geq0}$. Set
$X=X_0\times_{k_0}k$, and let $F$ be the
geometric Frobenius; for every
integer $i$ with $0\leq i\leq2d$ define

$$
V_{i,\ell}=H^i(X,\Ql),\qquad
F_{i,\ell}=F\vert_{V_{i,\ell}},\qquad
P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell}).
$$

The tuples $(V_{i,\ell},F_{i,\ell},P_{i,\ell})$ form the
smooth-proper
cohomological family, with
$V_{i,\ell}=H^i(X,\Ql)$, where this is the
ordinary cohomology group.
For every integer $i$ with $0\leq i\leq2d$, let $P_i(T)\in\mathbf Z[T]$ be the
normalized integral factor with
coefficient extension $P_i^{(\ell)}=P_{i,\ell}$, and put
$b_i=\deg P_i$, the Betti number.
There are Frobenius-equivariant isomorphisms

$$
H^0(X,\Ql)\cong\Ql,
\qquad
H^{2d}(X,\Ql)\cong\Ql(-d),
$$

where $\Ql(-d)$ is the
Tate twist of degree $-d$.
Geometric Frobenius acts by $1$ on the first space and, by the
Frobenius-on-twists
normalization, by $q^d$ on the second. Consequently

$$
P_0(T)=1-T,
\qquad
P_{2d}(T)=1-q^dT,
\qquad
b_0=b_{2d}=1.
$$

## Proof

Apply the perfect pairing in [prop-poincare-pairing] to degree zero and
top degree. The geometric-connectedness clause of
[def-weil-geometric-hypotheses], together with the constant-sheaf
finiteness statement [prop-cohomological-finiteness], gives
$H^0(X,\Ql)\cong\Ql$. The smooth orientation and twist normalization in
[prop-poincare-pairing], [def-coefficient-twists-detailed] give
$H^{2d}(X,\Ql)\cong\Ql(-d)$. The Frobenius convention in
[def-weil-smooth-proper-cohomological-family] gives the eigenvalue $1$
on $H^0$, while the twist action in
[def-weil-frobenius-coefficient-twists] gives the eigenvalue $q^d$
on $\Ql(-d)$. The factor and degree identifications in
[prop-integral-recovery], [def-weil-betti-numbers] give the displayed
factors and endpoint Betti numbers.
