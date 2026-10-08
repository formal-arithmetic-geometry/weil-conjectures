+++
id = "cor-zl-hasse-weil-general-bound"
kind = "theorem"
title = "Hasse–Weil bound in every dimension"
order = 2916
tags = ["latex:corollary"]
uses = ["cor-trf-point-counting", "cor-zl-hasse-bound", "def-weil-algebraically-closed-coefficients", "def-weil-betti-numbers", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-ordinary-reciprocal-roots", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "prop-endpoints", "prop-weight-purity-roots"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$, where $q=p^a$, and a prime $\ell\neq p$; write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$,
fix an isomorphism $\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and interpret
the $\Qlb$-objects in the
algebraically closed
coefficient category. Let $X_0/k_0$ be
smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq1}$, put
$X=X_0\times_{k_0}k$, let $F$ be the
global geometric Frobenius
in the geometric-Frobenius convention, and
let $(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ be the
smooth-proper
cohomological family extended to $\Qlb$, with
reciprocal roots taken in the
ordinary/reciprocal-root convention. Let
$b_i=\deg P_i=\dim_{\Qlb}H^i(X,\Qlb)$ be the
Betti numbers, and let
$N_n:=\#X_0(\mathbf F_{q^n})$ in the
point-count convention. Then, for every
integer $n\geq1$,

$$
\boxed{
\bigl|N_n-(q^{dn}+1)\bigr|\;\le\;\sum_{i=1}^{2d-1}b_i\,q^{in/2}}.
$$

In particular, for $n=1$,
$|N_1-q^d|\leq1+\sum_{i=1}^{2d-1}b_iq^{i/2}$, and for a curve ($d=1$,
$b_1=2g$) the bound reads $|N_n-(q^n+1)|\leq2g\,q^{n/2}$.

The endpoint term $1$ coming from $H^0$ cannot be dropped: for
$X_0=\mathbf P^1_{k_0}$ one has $d=1$, $b_1=0$ and $N_1=q+1$, so
$|N_1-q^d|=1>0=\sum_{i=1}^{2d-1}b_iq^{i/2}$. For $d=0$ the scheme
$X_0$ is $\operatorname{Spec}k_0$ and $N_n=1=q^{dn}$; the endpoints
$i=0$ and $i=2d$ coincide, which is why $d\geq1$ is assumed above.

## Proof

Step 1: the point-count identity. The scheme $X_0$ is proper, so by
[cor-trf-point-counting] applied to the constant sheaf,

$$
N_n=\sum_{i=0}^{2d}(-1)^i\Tr\bigl(F_{i,\ell}^n\mid V_{i,\ell}\bigr)
\quad\text{in }\Qlb .
$$

Step 2: the endpoint terms. By [prop-endpoints],
$P_0(T)=1-T$ and $P_{2d}(T)=1-q^dT$, and $b_0=b_{2d}=1$. Since
$P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell})$ is the coefficient
extension of $P_i$ ([def-weil-smooth-proper-cohomological-family],
[def-weil-betti-numbers]), the one-dimensional space $V_{0,\ell}$ has
Frobenius eigenvalue $1$ and the one-dimensional space $V_{2d,\ell}$ has
Frobenius eigenvalue $q^d$. As $d\geq1$, the degrees $0$ and $2d$ are
distinct, and

$$
\Tr\bigl(F_{0,\ell}^n\mid V_{0,\ell}\bigr)=1,
\qquad
\Tr\bigl(F_{2d,\ell}^n\mid V_{2d,\ell}\bigr)=q^{dn}.
$$

Since $2d$ is even, Step 1 becomes

$$
N_n-(q^{dn}+1)=\sum_{i=1}^{2d-1}(-1)^i
\Tr\bigl(F_{i,\ell}^n\mid V_{i,\ell}\bigr).
$$

Step 3: the middle terms. Fix $1\leq i\leq2d-1$ and let
$\alpha_{i,1},\ldots,\alpha_{i,b_i}$ be the eigenvalues of $F_{i,\ell}$
on $V_{i,\ell}$ with algebraic multiplicity; they are the reciprocal
roots of $P_{i,\ell}$, and there are $b_i=\deg P_{i,\ell}$ of them
([def-weil-smooth-proper-cohomological-family]). By
[prop-weight-purity-roots], $|\iota(\alpha_{i,j})|=q^{i/2}$ for every
$j$. The trace of $F_{i,\ell}^n$ is $\sum_j\alpha_{i,j}^n$ and $\iota$
is a field isomorphism, so the triangle inequality in $\mathbf C$ gives

$$
\Bigl|\iota\Tr\bigl(F_{i,\ell}^n\mid V_{i,\ell}\bigr)\Bigr|
\leq\sum_{j=1}^{b_i}|\iota(\alpha_{i,j})|^n=b_i\,q^{in/2}.
$$

Step 4: assembly. The left-hand side of the last display of Step 2 is
an integer, hence fixed by $\iota$. Applying $\iota$, the triangle
inequality and Step 3,

$$
\bigl|N_n-(q^{dn}+1)\bigr|
\leq\sum_{i=1}^{2d-1}\Bigl|\iota\Tr\bigl(F_{i,\ell}^n\mid V_{i,\ell}\bigr)\Bigr|
\leq\sum_{i=1}^{2d-1}b_i\,q^{in/2}.
$$

The case $n=1$ together with $|N_1-q^d|\leq|N_1-(q^d+1)|+1$ gives the
first particular statement. For $d=1$, the identity $b_1=2g$
is the dimension count in the proof of [cor-zl-hasse-bound], and the
bound specializes to the curve bound stated there.
