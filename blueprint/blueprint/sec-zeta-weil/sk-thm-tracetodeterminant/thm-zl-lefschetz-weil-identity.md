+++
id = "thm-zl-lefschetz-weil-identity"
kind = "theorem"
title = "Trace-to-determinant identity"
order = 2879
uses = ["cor-trf-point-counting", "def-weil-algebraically-closed-coefficients", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-ordinary-compact-cohomology", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "def-weil-weil-sheaf-complex", "lem-zl-log-det-identity"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$, where $q=p^a$, and a prime $\ell\neq p$; write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$,
and interpret the $\Qlb$-objects in the
algebraically closed
coefficient category. Let $X_0/k_0$ be
smooth, proper, geometrically
connected of pure dimension $d\in\mathbf Z_{\geq0}$, put
$X=X_0\times_{k_0}k$, and let $(\Qlb)_X$ be the constant
Weil sheaf with its canonical Weil
structure. Let $F$ be the
global geometric Frobenius
on the ordinary and
compact-support cohomology of $(\Qlb)_X$, in the
geometric-Frobenius convention. For every
$0\leq i\leq2d$, put

$$
V_i=H^i(X,\Qlb),\qquad F_i=F\vert_{V_i},\qquad
P_{i,\ell}(T)=\det(1-TF_i\mid V_i)\in\Qlb[T],
$$

the data obtained from the
smooth-proper
cohomological family by scalar extension. Let $Z(X_0,T)$ be the
point-count zeta series, and assume
the point-counting trace formula
[cor-trf-point-counting] of the trace-formula chapter for the constant Weil
sheaf. Then

$$
\boxed{
Z(X_0,T)=\prod_{i=0}^{2d}P_{i,\ell}(T)^{(-1)^{i+1}}}
\quad\text{in }\Qlb[[T]].
$$

## Proof

Step 1: the point-count identity. The scheme $X_0$ is proper, so by
[cor-trf-point-counting] applied to the constant Weil sheaf
$(\Qlb)_X$, for every $n\geq1$,

$$
N_n:=\#X_0(\mathbf F_{q^n})
=\sum_{i\in\mathbf Z}(-1)^i\Tr\bigl(F^n\mid H^i(X,\Qlb)\bigr)
=\sum_{i=0}^{2d}(-1)^i\Tr(F_i^n\mid V_i),
$$

the second identity being the finite-dimensionality, the vanishing
outside $0\leq i\leq2d$, and the identification
$V_i=H^i(X,\Qlb)$, $F_i=F|_{V_i}$, supplied by
[def-weil-ordinary-compact-cohomology] (compactly supported
cohomology being the ordinary one for proper $X_0$, per that
definition) and by [def-weil-smooth-proper-cohomological-family]
after scalar extension to $\Qlb$.

Step 2: the logarithm of the zeta series. By
[def-weil-point-counts-zeta],

$$
Z(X_0,T)=\exp\left(\sum_{n\geq1}N_n\frac{T^n}{n}\right),
$$

so that, the formal logarithm and the exponential being mutually
inverse on $T\Qlb[[T]]$ and $1+T\Qlb[[T]]$,

$$
\log Z(X_0,T)=\sum_{n\geq1}N_n\frac{T^n}{n}.
$$

Step 3: substitution and interchange. Inserting Step 1 and using that
the sum over $i=0,\ldots,2d$ is finite while the coefficientwise sums
over $n$ are formal,

$$
\log Z(X_0,T)
=\sum_{n\geq1}\sum_{i=0}^{2d}(-1)^i\Tr(F_i^n\mid V_i)\frac{T^n}{n}
=\sum_{i=0}^{2d}(-1)^i
\left(\sum_{n\geq1}\Tr(F_i^n\mid V_i)\frac{T^n}{n}\right).
$$

Step 4: the per-degree logarithm. For every $i$, the pair
$(V_i,F_i)$ is a Frobenius module, so [lem-zl-log-det-identity]
gives

$$
\sum_{n\geq1}\Tr(F_i^n\mid V_i)\frac{T^n}{n}
=-\log P_{i,\ell}(T).
$$

Hence, by the additivity of the formal logarithm on finite products of
series with constant coefficient $1$,

$$
\log Z(X_0,T)
=\sum_{i=0}^{2d}(-1)^{i+1}\log P_{i,\ell}(T)
=\log\left(\prod_{i=0}^{2d}P_{i,\ell}(T)^{(-1)^{i+1}}\right).
$$

Step 5: exponentiation. Both sides of the identity of Step 4 have the
same logarithm and lie in $1+T\Qlb[[T]]$, so applying the formal
exponential, which is inverse to the logarithm on that set, gives the
displayed identity.
