+++
id = "prop-integral-recovery"
kind = "theorem"
title = "Integral factor recovery"
order = 2910
tags = ["latex:proposition"]
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-normalized-integral-fraction", "def-weil-ordinary-compact-cohomology", "def-weil-parity-products", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "thm-weil-realization-independence"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$ and
$k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix an indeterminate $T$.
Let $X_0/k_0$ be
smooth, proper, and geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, and put
$X=X_0\times_{k_0}k$. For every prime
$\ell\neq p$, let
$\Ql=\mathbf Q_\ell$, and, for $P(T)=\sum_r c_rT^r\in\mathbf Z[T]$, write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$ for its coefficientwise
extension, and let
$(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ be the
smooth-proper
cohomological family. Define the
point-count zeta series by

$$
Z(X_0,T)=\exp\left(\sum_{n\geq1}
\#X_0(\mathbf F_{q^n})\frac{T^n}{n}\right),
$$

and write its
normalized reduced integral
presentation as

$$
Z(X_0,T)=\frac{A(T)}{B(T)},\qquad
A,B\in\mathbf Z[T],\quad A(0)=B(0)=1,
\quad\gcd(A,B)=1\text{ in }\mathbf Q[T].
$$

For every prime $\ell\neq p$, define the
odd and even parity products

$$
N_\ell(T)=\prod_{\substack{0\leq i\leq2d\\i\text{ odd}}}P_{i,\ell}(T),
\qquad
D_\ell(T)=\prod_{\substack{0\leq i\leq2d\\i\text{ even}}}P_{i,\ell}(T).
$$

There are unique polynomials

$$
P_i(T)\in\mathbf Z[T]
\qquad(0\leq i\leq2d)
$$

with $P_i(0)=1$ and $P_i^{(\ell)}=P_{i,\ell}$ for every
$\ell\neq p$. These are the
integral Frobenius factors.
For every $\ell\neq p$,

$$
A^{(\ell)}=N_\ell,
\qquad
B^{(\ell)}=D_\ell.
$$

The resulting factors satisfy

$$
Z(X_0,T)=
\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}
\quad\text{in }\mathbf Q(T),
$$

and

$$
\deg P_i=\dim_{\Ql}H^i(X,\Ql)
$$

where $H^i(X,\Ql)$ denotes the
ordinary cohomology group,
for every $\ell\neq p$.

## Proof

The terminal realization-independent factor interface
[thm-weil-realization-independence] supplies, for every $i$, a unique
integral polynomial $P_i$ whose scalar extension is $P_{i,\ell}$ for every
$\ell\neq p$. Its normalization and the parity products are the
normalizations in [def-weil-integral-frobenius-factor] and
[def-weil-parity-products]; the normalized fraction is the one in
[def-weil-normalized-integral-fraction]. Thus
[def-weil-point-counts-zeta] gives

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}
$$

after scalar extension, and uniqueness of the normalized fraction gives
$A^{(\ell)}=N_\ell$ and $B^{(\ell)}=D_\ell$. The degree of
$P_{i,\ell}$ is $\dim_{\Ql}H^i(X,\Ql)$ by
[def-weil-smooth-proper-cohomological-family]; scalar extension preserves
degree, so the displayed degree equality follows. All objects and
identifications used here are formed with the finite-field and geometric
hypotheses in [def-weil-finite-field-fiber],
[def-weil-geometric-hypotheses], and the ordinary cohomology convention
[def-weil-ordinary-compact-cohomology].
