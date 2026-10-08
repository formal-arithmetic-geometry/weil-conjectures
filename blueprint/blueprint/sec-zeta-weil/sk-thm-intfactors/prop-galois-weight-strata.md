+++
id = "prop-galois-weight-strata"
kind = "theorem"
title = "Galois stability of the weight strata"
order = 2906
tags = ["latex:proposition"]
uses = ["def-weil-algebraic-closure-q", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-normalized-integral-fraction", "def-weil-numbers", "def-weil-ordinary-reciprocal-roots", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "lem-embedding-extension"]
+++
Fix the finite-field datum
$p$, $a\in\mathbf Z_{\geq1}$, $q=p^a$, $k_0=\Fq$, and let
$k=\Fbar$ be the fixed algebraic closure of $k_0$, a
prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, and choose an algebraic
closure $\Qlb$ of $\Ql$, and an
algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$. Put

$$
\overline{\mathbf Q}^{(\ell)}
=\{z\in\Qlb:z\text{ is algebraic over }\mathbf Q\}.
$$

For $\alpha\in\overline{\mathbf Q}^{\times}$ and $i\in\mathbf Z$, call
$\alpha$ a $q$-Weil number of weight $i$ when

$$
|\tau(\alpha)|=q^{i/2}
\quad\text{for every }\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C;
$$

this is the Weil-number condition, and the
algebraic-closure convention fixes
the ell-adic comparison field. Let $X_0/k_0$ be
smooth, proper, geometrically connected
of pure dimension
$d\in\mathbf Z_{\geq0}$, put $X=X_0\times_{k_0}k$, and let
$(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ be the
smooth-proper
cohomological family.
Fix indeterminates $T$ and $U$.
Let $Z(X_0,T)$ be the
point-count zeta series.
Let $A,B\in\mathbf Z[T]$ satisfy

$$
Z(X_0,T)=A(T)/B(T),\qquad A(0)=B(0)=1,\qquad
\gcd(A,B)=1\text{ in }\mathbf Q[T],
$$

the normalized integral-fraction
conditions; fix such a normalized presentation. For
$C\in\{A,B\}$, let
$r=\deg C$ and define its reciprocal polynomial

$$
C^\#(U)=U^rC(U^{-1})
$$

Its roots, with multiplicity, are the reciprocal roots in the
reciprocal-root convention;
their inverses are the corresponding ordinary roots. For every integer $i$ with
$0\leq i\leq2d$, define

$$
R_i=
\begin{cases}
\text{the submultiset of roots of \(A^\#\) that are \(q\)-Weil numbers
of weight \(i\)},& i\text{ odd},\\
\text{the submultiset of roots of \(B^\#\) that are \(q\)-Weil numbers
of weight \(i\)},& i\text{ even}.
\end{cases}
$$

Assume that every reciprocal root occurring in $A^\#$ or $B^\#$ has a
unique weight in $\{0,\ldots,2d\}$, and that the displayed $q$-Weil
condition is invariant under every embedding of its number field into
$\mathbf C$. Then for every integer $i$ with $0\leq i\leq2d$ each
$R_i$ is stable, with multiplicities, under
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$.

## Proof

The polynomials $A^\#,B^\#$ of
[def-weil-ordinary-reciprocal-roots] have rational coefficients,
so their root multisets are stable under
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, and by
[lem-embedding-extension] the $q$-Weil condition of weight $i$
of [def-weil-numbers] is Galois-stable. Hence, for each $i$,
the submultiset $R_i$ is stable under
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, with
multiplicities, which is the assertion.
