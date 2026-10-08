+++
id = "prop-functional-equation"
kind = "theorem"
title = "Functional equation"
order = 2922
tags = ["latex:proposition"]
uses = ["def-weil-determinant-constants", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-functional-equation-sign", "def-weil-geometric-hypotheses", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "prop-duality-reciprocity", "prop-trace-determinant"]
+++
Let $p$ be prime, let $a\in\mathbf Z_{\geq1}$, put $q=p^a$, and set
$k_0=\Fq$; let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Fix a prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and fix an
indeterminate $T$. For $P(T)=\sum_r c_rT^r\in\mathbf Z[T]$, write
$P^{(\ell)}(T)=\sum_r(c_r\cdot1_{\Ql})T^r$ for coefficientwise extension.
Let $X_0/k_0$ be a
smooth, proper, geometrically
connected scheme of pure dimension
$d\in\mathbf Z_{\geq0}$; put $X=X_0\times_{k_0}k$. Let $F$ be
geometric Frobenius. For every integer $i$
with $0\leq i\leq2d$, put

$$
V_{i,\ell}=H^i(X,\Ql),
\qquad
F_{i,\ell}=F\vert_{V_{i,\ell}},
\qquad
P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell}).
$$

Here $H^i(X,\Ql)$ is the
ordinary cohomology group.
These data form the
smooth-proper
cohomological family. Let $P_i(T)\in\mathbf Z[T]$ be the
integral Frobenius factor
with $P_i(0)=1$ and $P_i^{(\ell)}=P_{i,\ell}$. Put
$b_i=\deg P_i$ and define the
determinant constant
$D_i=(-1)^{b_i}[T^{b_i}]P_i(T)$. Define

$$
\chi=\sum_{i=0}^{2d}(-1)^ib_i,
\qquad
\Delta=\prod_{i=0}^{2d}D_i^{(-1)^i},
\qquad
\varepsilon=(-1)^\chi q^{-d\chi/2}\Delta.
$$

Thus $\varepsilon$ is the
normalized functional-equation
sign. Define the point-count zeta
series by

$$
Z(X_0,T)=\exp\left(\sum_{n\geq1}
\#X_0(\mathbf F_{q^n})\frac{T^n}{n}\right).
$$

The alternating determinant scalar satisfies

$$
\Delta^2=q^{d\chi}.
$$

The normalized sign satisfies

$$
\varepsilon^2=1,\qquad \varepsilon\in\{1,-1\},
$$

and the zeta function satisfies

$$
Z(X_0,q^{-d}T^{-1})
=\varepsilon q^{d\chi/2}T^\chi Z(X_0,T)
\quad\text{in }\mathbf Q(T).
$$

Equivalently, the determinant-constant form of the functional equation is

$$
Z(X_0,q^{-d}T^{-1})
=(-1)^\chi T^\chi
\left(\prod_{i=0}^{2d}D_i^{(-1)^i}\right)Z(X_0,T).
$$

## Proof

1. **1.** The exponential series defining $Z(X_0,T)$ is the
point-count zeta series of [def-weil-point-counts-zeta]; the
trace-to-determinant calculation in
[prop-trace-determinant] identifies it with the normalized product
$$
Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}.
$$
All subsequent manipulations therefore take place in the Laurent rational
function field $\mathbf Q(T)$.
1. **2.** The reciprocity relations in
[prop-duality-reciprocity] give
$$
b_i=b_{2d-i},\qquad D_iD_{2d-i}=q^{db_i},\qquad
P_i(q^{-d}T^{-1})
=(-1)^{b_i}T^{-b_i}D_{2d-i}^{-1}P_{2d-i}(T),
$$
where the last equality is the displayed relation with $i$ replaced by
$2d-i$. Reindexing the product in Step 1 by $i\mapsto2d-i$, and using
$(-1)^{2d-i}=(-1)^i$, gives
$$
\begin{aligned}
Z(X_0,q^{-d}T^{-1})
&=\prod_{i=0}^{2d}
\left((-1)^{b_i}T^{-b_i}D_{2d-i}^{-1}P_{2d-i}(T)\right)^{(-1)^{i+1}}\\
&=(-1)^\chi T^\chi
\left(\prod_{i=0}^{2d}D_i^{(-1)^i}\right)Z(X_0,T).
\end{aligned}
$$
These same reciprocity relations show that $d\chi$ is even. This is
immediate if $d$ is even. If $d$ is odd, then
[prop-duality-reciprocity] gives that $b_d$ is even, while pairing
the terms indexed by $i$ and $2d-i$ gives
$$
\chi=
2\sum_{0\leq i<d}(-1)^ib_i+(-1)^db_d,
$$
which is even. Thus the normalized sign in
[def-weil-functional-equation-sign] is defined.
The determinant-constant definition in
[def-weil-functional-equation-sign] names the product in parentheses
$\Delta$, and the same definition gives
$$
\varepsilon=(-1)^\chi q^{-d\chi/2}\Delta.
$$
The determinant relation also implies
$$
\Delta^2
=\prod_{i=0}^{2d}(D_iD_{2d-i})^{(-1)^i}
=\prod_{i=0}^{2d}q^{db_i(-1)^i}
=q^{d\chi}.
$$
1. **3.** Squaring the preceding normalization and using
[def-weil-functional-equation-sign] yields
$$
\varepsilon^2
=(-1)^{2\chi}q^{-d\chi}\Delta^2=1.
$$
Since $\varepsilon\in\mathbf Q^\times$, it follows that
$\varepsilon\in\{1,-1\}$.
1. **4.** Substituting
$(-1)^\chi\Delta=\varepsilon q^{d\chi/2}$ into the product identity of
Step 2 gives
$$
Z(X_0,q^{-d}T^{-1})
=\varepsilon q^{d\chi/2}T^\chi Z(X_0,T).
$$
Replacing $\Delta$ by its defining product from
[def-weil-functional-equation-sign] gives equivalently
$$
Z(X_0,q^{-d}T^{-1})
=(-1)^\chi T^\chi
\left(\prod_{i=0}^{2d}D_i^{(-1)^i}\right)Z(X_0,T),
$$
which proves both asserted forms.
