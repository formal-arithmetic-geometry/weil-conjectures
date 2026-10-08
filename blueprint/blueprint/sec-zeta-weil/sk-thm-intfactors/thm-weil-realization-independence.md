+++
id = "thm-weil-realization-independence"
kind = "theorem"
title = "Realization-independent integral factors"
order = 2909
uses = ["cor-trf-point-counting", "def-weil-algebraic-closure-q", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-hankel-matrix", "def-weil-integral-frobenius-factor", "def-weil-normalized-integral-fraction", "def-weil-numbers", "def-weil-ordinary-reciprocal-roots", "def-weil-parity-products", "def-weil-point-counts-zeta", "def-weil-smooth-proper-cohomological-family", "lem-embedding-extension", "lem-zl-log-det-identity", "prop-euler-product", "prop-galois-weight-strata-identification", "prop-galois-weight-strata-integrality", "prop-weight-purity-roots", "prop-weight-separation", "prop-weil-rationality-criterion", "prop-weil-reciprocal-roots-eigenvalues", "prop-weil-zeta-normalized-presentation", "thm-weil-deligne-purity", "thm-zl-lefschetz-weil-identity"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, put
$q=p^a$, $k_0=\Fq$, and let $k=\Fbar$ be the
fixed algebraic closure of $k_0$.
Let
$X_0/k_0$ be smooth, proper,
geometrically connected of pure dimension $d\in\mathbf Z_{\geq0}$, and
put $X=X_0\times_{k_0}k$. Fix an indeterminate $T$. For every prime
$\ell\neq p$, let
$(V_{i,\ell},F_{i,\ell},P_{i,\ell})_{0\leq i\leq2d}$ be the
smooth-proper
cohomological family. The reciprocal-root multiset is interpreted using the
ordinary and reciprocal-root
convention, and each $P_{i,\ell}$ is the determinant factor in that
cohomological family, explicitly

$$
P_{i,\ell}(T)=\det(1-TF_{i,\ell}\mid V_{i,\ell}).
$$

Let $Z(X_0,T)$ be the
point-count zeta series, and write
$Z(X_0,T)=A(T)/B(T)$ with $A,B\in\mathbf Z[T]$, $A(0)=B(0)=1$,
$\gcd(A,B)=1$ in $\mathbf Q[T]$; this is a chosen presentation satisfying
the normalized integral-fraction
conditions. Fix an algebraic closure $\overline{\mathbf Q}$. For each
$\ell\neq p$, write $\Ql=\mathbf Q_\ell$, choose an algebraic closure
$\Qlb$ of $\Ql$, set
$\overline{\mathbf Q}^{(\ell)} =\{\alpha\in\Qlb:\alpha\text{ is algebraic over }\mathbf Q\}$, the
algebraic closure of $\mathbf Q$
inside $\Qlb$, and choose an isomorphism
$\jmath_\ell:\overline{\mathbf Q}\xrightarrow{\sim} \overline{\mathbf Q}^{(\ell)}$.
For $C\in\{A,B\}$, put
$r_C=\deg C$ and define its reciprocal polynomial by

$$
C^\#(U)=U^{r_C}C(U^{-1}).
$$

For each $0\leq i\leq2d$, form the multiset
ordinary roots $R_i$ of
$A^\#$ when $i$ is odd and of $B^\#$ when $i$ is even whose elements
are $q$-Weil numbers of weight $i$; the
intrinsic weights and the Galois stability of these multisets are
proved in *Intrinsic weights of the reciprocal roots* below. Put

$$
Q_i(T)=\prod_{\alpha\in R_i}(1-\alpha T)\in\mathbf Z[T].
$$

These $Q_i$ are candidate normalized integral factors.
For every
prime $\ell\neq p$, every ell-adic realization
$\jmath_\ell:\overline{\mathbf Q}\xrightarrow{\sim}\overline{\mathbf Q}^{(\ell)}$,
and every $0\leq i\leq2d$, write
$Q_i^{(\ell,\jmath_\ell)}$ for the scalar extension of $Q_i$ along
$\jmath_\ell$.
Then scalar extension identifies the reciprocal-root multiset of $Q_i$ with
that of $P_{i,\ell}$:

$$
Q_i^{(\ell,\jmath_\ell)}(T)=P_{i,\ell}(T).
$$

Here $Q_i^{(\ell,\jmath_\ell)}$ means coefficientwise extension along
$\jmath_\ell:\overline{\mathbf Q}\xrightarrow{\sim} \overline{\mathbf Q}^{(\ell)}$, so the displayed equality is an equality in
the chosen algebraic closure of $\Ql$ (with $P_{i,\ell}$ viewed through
$\Ql\subset\Qlb$).
Consequently, after these scalar identities are established, each $Q_i$ is
the normalized
integral Frobenius factor
for the common realization.
These scalar identities are independent of the chosen realization and
preserve the normalization $Q_i(0)=1$. If
$N_\ell(T)=\prod_{\substack{0\leq i\leq2d\\i\ {\rm odd}}}P_{i,\ell}(T)$ and
$D_\ell(T)=\prod_{\substack{0\leq i\leq2d\\i\ {\rm even}}}P_{i,\ell}(T)$, the
parity-product construction gives
$A^{(\ell)}=N_\ell$ and $B^{(\ell)}=D_\ell$. No additional assertion
about Frobenius operators is made by this scalar comparison.
The scalar-extension notation is coefficientwise extension of integral
polynomials.

## Proof

*Step 1: the point counts are independent of $\ell$.* The
setting is the smooth, proper, geometrically connected $X_0/k_0$ of
pure dimension $d$ of [def-weil-geometric-hypotheses], in the
datums of [def-weil-finite-field-fiber], and the
integer point counts $N_n(X_0)=\#X_0(\mathbf F_{q^n})$ do not
involve $\ell$, by the point-count convention of
[def-weil-point-counts-zeta]; hence the zeta series
$Z(X_0,T)$ lies in $1+T\mathbf Z[[T]]$, and by the closed-point
product of [prop-euler-product] it is the Taylor series of the
closed-point product. For each $\ell\neq p$, the point-count trace
formula of [cor-trf-point-counting] and the
[lem-zl-log-det-identity] log-determinant identity yield the
[thm-zl-lefschetz-weil-identity] trace-to-determinant identity

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_{i,\ell}(T)^{(-1)^{i+1}}
\quad\text{in }\Ql[[T]],
$$

after the scalar extension to the $\Ql$-coefficients of
[def-weil-smooth-proper-cohomological-family], with the root
convention of [def-weil-ordinary-reciprocal-roots]. Since the
right-hand side is rational over $\Ql$, its Taylor coefficients
satisfy a linear recurrence over $\Ql$, and its
[def-weil-hankel-matrix] has some finite rank $r$ over $\Ql$.
Every finite minor of order $r+1$ has integer entries and
vanishes in $\Ql$, hence already in $\mathbf Q$.
Thus its rank over $\mathbf Q$ is at most $r$, and by the
rationality criterion of
[prop-weil-rationality-criterion] the series lies in
$\mathbf Q(T)$; the normalized reduced integral presentation of
[def-weil-normalized-integral-fraction] is then the unique one
supplied by [prop-weil-zeta-normalized-presentation].

*Step 2: weight separation.* By [prop-weil-reciprocal-roots-eigenvalues]
the reciprocal roots of $P_{i,\ell}$ are the eigenvalues of
$F_{i,\ell}$, and [thm-weil-deligne-purity] gives
$|\iota(\alpha)|=q^{i/2}$ for every such eigenvalue, for the fixed
isomorphism $\iota:\Qlb\xrightarrow{\sim}\mathbf C$ used there.
The hypotheses of [prop-weight-separation] therefore hold:
every reciprocal root of $P_{i,\ell}$ satisfies
$|\iota(\alpha)|=q^{i/2}$, and the trace-to-determinant identity of
Step 1 holds. Concretely, the polynomials $P_{i,\ell}$,
$P_{j,\ell}$ are coprime for $i\neq j$, the parity products
$N_\ell,D_\ell$ of [def-weil-parity-products]
are coprime with constant coefficient $1$,
$Z(X_0,T)=N_\ell(T)/D_\ell(T)$, and the ordinary root multiset of
each $P_{i,\ell}$ is exactly the submultiset of roots of the
appropriate parity product with the weight-$i$ absolute-value
condition.

*Step 3: the parity products are the normalized presentation.*
Both $A^{(\ell)}/B^{(\ell)}$ and $N_\ell/D_\ell$ are reduced
fractions —$\gcd(A,B)=1$ in $\mathbf Q[T]$ by
[def-weil-normalized-integral-fraction], $\gcd(N_\ell,D_\ell)=1$
by Step 2 —with constant coefficients $1$, and both equal the
Taylor series $Z(X_0,T)$ in $\Ql[[T]]$. Cross multiplication
and coprimality over $\Ql[T]$ show that the numerators and
denominators differ by the same scalar. Their constant terms
are $1$, so that scalar is $1$. Consequently
$A^{(\ell)}=N_\ell$ and $B^{(\ell)}=D_\ell$ coefficientwise in
$\Ql$, after extension along the [def-weil-algebraic-closure-q]
identification $\jmath_\ell$ of [def-weil-finite-field-fiber]'s
datum. This is the parity-product clause.

*Step 4: the weight strata and the stratum polynomials.* By
*Intrinsic weights of the reciprocal roots* below, every root of $A^\#$ or $B^\#$ has a
unique weight in $\{0,\ldots,2d\}$, and the resulting root multisets
$R_i$ are Galois-stable. Hence
[prop-galois-weight-strata-integrality] and
[prop-galois-weight-strata-identification] apply and return that the
normalized stratum polynomials

$$
Q_i(T)=\prod_{\alpha\in R_i}(1-\alpha T)
$$

lie in $\mathbf Z[T]$ and that the reciprocal-root multiset of $Q_i$
is the weight-$i$ submultiset of the roots of $A^\#$
($i$ odd) or of $B^\#$ ($i$ even). This is the integrality clause
for the stratum polynomials.

*Step 5: the scalar identities.* For fixed
$\ell\neq p$ and $\jmath_\ell$, the scalar extension
$Q_i^{(\ell,\jmath_\ell)}$ is the product over the identified
weight-$i$ submultiset of roots of $A^{(\ell)\#}=N_\ell^\#$
($i$ odd) or of $B^{(\ell)\#}=D_\ell^\#$ ($i$ even), which by
the multiset identification of Step 2 is exactly the reciprocal-root
multiset of $P_{i,\ell}$; both polynomials have constant
coefficient $1$, so

$$
Q_i^{(\ell,\jmath_\ell)}(T)=P_{i,\ell}(T),
$$

the identity of the interface statement. The independence of the
identity from the chosen realization and realization isomorphism is
the uniqueness in Step 4, and $Q_i(0)=1$ is the normalization
$Q_i(0)=\prod_{\alpha\in R_i}1=1$. With Step 3 this establishes
the assertion, and $Q_i$ is the integral Frobenius factor of
[def-weil-integral-frobenius-factor]
in degree $i$: its scalar extension along $\jmath_\ell$ is
$P_{i,\ell}$ for every $\ell\neq p$.

## Intrinsic weights of the reciprocal roots

In the situation of [thm-weil-realization-independence], every root of
$A^\#$ or $B^\#$ has a unique weight in $\{0,\ldots,2d\}$, and the
resulting multisets $R_i$ of
ordinary roots that are
$q$-Weil numbers of weight $i$ are stable
under $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$.

*Proof.*
In the situation of [thm-weil-realization-independence] the fraction
$A^{(\ell)}/B^{(\ell)}$ and the parity products $N_\ell/D_\ell$ of
[prop-weight-separation] both equal the series $Z(X_0,T)$ in
$\Ql[[T]]$; here $\gcd(A,B)=1$ in $\mathbf Q[T]$ by
[def-weil-normalized-integral-fraction], while $\gcd(N_\ell,D_\ell)=1$
and $N_\ell(0)=D_\ell(0)=1$ by [prop-weight-separation]. Cross
multiplication over $\Ql[T]$ and coprimality therefore give
$A^{(\ell)}=N_\ell$ and $B^{(\ell)}=D_\ell$. Hence every root of
$A^\#$ or $B^\#$ maps under $\jmath_\ell$ to a root of $N_\ell^\#$
or $D_\ell^\#$ in the [def-weil-ordinary-reciprocal-roots]
convention, that is, to a reciprocal root of exactly one of the factors
$P_{i,\ell}$ (distinct $P_{i,\ell}$ being coprime by
[prop-weight-separation]); the weight of that factor is a weight of
the root, because every root of $P_{i,\ell}$ has absolute value
$q^{i/2}$ by [prop-weight-purity-roots] and an arbitrary complex
embedding of the number field generated by the root extends to an
isomorphism of algebraic closures by [lem-embedding-extension]. For
the same reason the weight is independent of the chosen $\ell$ and
realization, the $q$-Weil condition of [def-weil-numbers] being
stable under $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$ and
under every embedding of its number field into $\mathbf C$; the
conditions of distinct weights are mutually exclusive because
$q^{i/2}\neq q^{j/2}$ for $i\neq j$. Each root of $A^\#$ or $B^\#$
therefore has a unique weight in $\{0,\ldots,2d\}$, and the multisets
$R_i$ of [thm-weil-realization-independence] are stable under
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$.
