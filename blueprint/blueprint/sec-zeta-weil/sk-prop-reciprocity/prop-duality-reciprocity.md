+++
id = "prop-duality-reciprocity"
kind = "theorem"
title = "Duality reciprocity"
order = 2919
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-weil-betti-numbers", "def-weil-determinant-constants", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-poincare-trace-cup", "def-weil-smooth-proper-cohomological-family", "lem-weil-alternating-form-dimension", "prop-poincare-pairing"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$; let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and for
$P(T)=\sum_r c_rT^r\in\mathbf Z[T]$ write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$ for coefficientwise extension.
Let
$X_0/k_0$ be smooth,
proper, and geometrically connected of pure dimension
$d\in\mathbf Z_{\geq0}$, let $X=X_0\times_{k_0}k$, and let $F$ be the
geometric Frobenius. Fix an indeterminate
$T$. For every integer $i$ with $0\leq i\leq2d$, put
$V_{i,\ell}=H^i(X,\Ql)$, where $H^i(X,\Ql)$ denotes the
ordinary cohomology group,
and set $P_{i,\ell}(T)=\det(1-TF\mid V_{i,\ell})$. Let
$P_i(T)\in\mathbf Z[T]$ be the
normalized integral factor
with $P_i^{(\ell)}=P_{i,\ell}$; these determinant data are the
smooth-proper
cohomological family. Put
$b_i=\deg P_i$, and set

$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T).
$$

Let $\langle-,-\rangle_i$ be the
trace–cup-product pairing. Poincare
duality identifies
the multiset of
Frobenius eigenvalues in degree $2d-i$ with

$$
\left\{\frac{q^d}{\alpha}:\alpha
\text{ is an eigenvalue in degree }i\right\},
$$

including algebraic multiplicity. Moreover,

$$
b_i=b_{2d-i},
\qquad
D_iD_{2d-i}=q^{db_i},
$$

and the integral factors satisfy the Laurent-polynomial identity

$$
P_{2d-i}(q^{-d}T^{-1})
=(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T)
\quad\text{in }\mathbf Q[T,T^{-1}].
$$

For the middle degree $i=d$, the pairing is $(-1)^d$-symmetric. In particular,
if $d$ is odd, then $b_d$ is even.

## Proof

1. **1.** Write $V_i=H^i(X,\Ql)$, put
$n_i=\dim_{\Ql}V_i$, and let
$\alpha_{i,1},\ldots,\alpha_{i,n_i}$ denote the eigenvalues of $F$ on
$V_i$, counted with algebraic multiplicity. The perfect,
Frobenius-similitude pairing in [prop-poincare-pairing] induces
$$
V_{2d-i}\xrightarrow{\sim}V_i^\vee(-d),\qquad
y\longmapsto\bigl(x\longmapsto\langle x,y\rangle_i\bigr).
$$
Since $F$ acts on $\Ql(-d)$ by $q^d$, the operator transported to the
right-hand side is $q^d(F^{-1})^\vee$. Its eigenvalue multiset is
$$
\{\alpha_{2d-i,1},\ldots,\alpha_{2d-i,n_{2d-i}}\}
=
\{q^d/\alpha_{i,1},\ldots,q^d/\alpha_{i,n_i}\}.
$$
In particular the two multisets have the same cardinality.
1. **2.** By the Betti-number convention in
[def-weil-betti-numbers], $b_j=\dim_{\Ql}V_j=n_j$. The cardinality
comparison in Step 1 therefore gives
$$
b_{2d-i}=b_i.
$$
The determinant-constant definition in
[def-weil-determinant-constants] and the factorization
$P_i(T)=\prod_{r=1}^{b_i}(1-\alpha_{i,r}T)$ give
$$
D_i=(-1)^{b_i}[T^{b_i}]P_i(T)
=\prod_{r=1}^{b_i}\alpha_{i,r}.
$$
Using the reciprocal multiset from Step 1,
$$
D_{2d-i}
=\prod_{r=1}^{b_i}\frac{q^d}{\alpha_{i,r}}
=\frac{q^{db_i}}{D_i},
$$
and hence $D_iD_{2d-i}=q^{db_i}$.
1. **3.** The same factorization gives, as an identity in
$\mathbf Q[T,T^{-1}]$,
$$
\begin{aligned}
P_{2d-i}(q^{-d}T^{-1})
&=\prod_{r=1}^{b_i}
\left(1-\frac{1}{\alpha_{i,r}}T^{-1}\right)\\
&=(-1)^{b_i}T^{-b_i}
\left(\prod_{r=1}^{b_i}\alpha_{i,r}\right)^{-1}
\prod_{r=1}^{b_i}(1-\alpha_{i,r}T)\\
&=(-1)^{b_i}T^{-b_i}D_i^{-1}P_i(T).
\end{aligned}
$$
This is the claimed Laurent-polynomial reciprocity.
1. **4.** For $i=d$, the symmetry clause of
[prop-poincare-pairing] makes the pairing $(-1)^d$-symmetric. If
$d$ is odd, choose a nonzero $\Ql$-linear trivialization
$\Ql(-d)\xrightarrow{\sim}\Ql$; this is possible because the Tate-twist
construction in [def-coefficient-twists-detailed] makes
$\Ql(-d)$ an invertible rank-one coefficient space. Transporting the
pairing along this trivialization gives a nondegenerate alternating
$\Ql$-valued form on $V_d$. The
coefficient field is $\Ql=\mathbf Q_\ell$, of characteristic zero under
the finite-field convention of [def-weil-finite-field-fiber], so its
characteristic is not $2$. Applying
[lem-weil-alternating-form-dimension] gives
$\dim_{\Ql}V_d$ even; [def-weil-betti-numbers] then gives that
$b_d$ is even.
