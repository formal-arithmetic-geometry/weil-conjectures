+++
id = "sk-thm-intfactors"
kind = "section"
title = "Integral Frobenius factors"
order = 2901
lean = ["AlgebraicGeometry.IsWeilFactorization.unique", "TraceDatum.exists_isWeilFactorization"]
uses = ["sk-def-cohfamily", "sk-def-roots", "sk-prop-rootpurity", "sk-prop-separation", "sk-thm-rationality"]
+++
*Theorem (sketch).*

For every $0\le i\le2d$ there is a unique polynomial $P_i(T)\in\Z[T]$ with
$P_i(0)=1$ such that for *every* prime $\ell\ne p$

$$
P_i^{(\ell)}(T)=\det\bigl(1-TF_{i,\ell}\mid H^{i}(X,\Ql)\bigr),
$$

and then

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}},
$$

a factorization that is independent of $\ell$.

## Proof

By [sk-thm-rationality], $Z\in\Q(T)\cap(1+T\Z[[T]])$. *Fatou's
lemma* (Fatou, Acta Math. 30 (1906); in the expanded blueprint
`prop-weil-integral-rational-series`) upgrades this to a
normalized integral presentation: a rational power series with
*integer* coefficients can be written $Z=A/B$ with $A,B\in\Z[T]$,
$B(0)=1$ and $\gcd(A,B)=1$ in $\Q[T]$, and then $A(0)=Z(0)=1$. Sketch:
the coefficients $z_n$ satisfy a linear recurrence, and since they are
integers the shift operator on the span of the shifted sequences has an
integer matrix $M$ in a basis of the lattice they generate, so
$Z=e\,\operatorname{adj}(I-TM)v/\det(I-TM)$ with integral numerator and
denominator of constant term $1$; by Gauss's lemma their greatest common
divisor can be taken primitive in $\Z[T]$, and it then divides both in
$\Z[T]$ and has constant term $\pm1$, so cancelling it leaves a coprime
integral presentation. The presentation is unique, by coprimality and the
normalization of the constant terms. By [sk-prop-rootpurity] the
reciprocal roots of the $\ell$-adic factors carry the weights $q^{i/2}$,
which are pairwise distinct for distinct $i$, so [sk-prop-separation]
separates the factors: $A/B$ and the parity presentation $N_\ell/D_\ell$ of
[sk-prop-separation] are both coprime presentations of $Z$ with constant
terms $1$, hence $A=N_\ell$ and $B=D_\ell$ in $\Ql[T]$, so the roots of $A$,
resp. $B$, are the ordinary roots of the $P_{j,\ell}$ with $j$ odd, resp.
even, and the multiplicity of each root in $A$ or $B$ determines its weight,
hence its index $j$: a root of $A$ or $B$ is an ordinary root
$\beta=\alpha^{-1}$ with $\alpha$ an eigenvalue of $F$ on some $V_{j,\ell}$,
and $j$ is determined by $|\iota(\alpha)|=q^{j/2}$, which is
[sk-prop-rootpurity]. Two points have to be supplied to conclude
$P_i\in\Z[T]$. *(i) Rationality.* $\Gal(\overline\Q/\Q)$ permutes the
roots of the rational polynomials $A$ and $B$, and it preserves each weight
stratum, because the weight of $\alpha$ is intrinsic:
$|\tau(\alpha)|=q^{j/2}$ for *every* embedding $\tau$ of $\Q(\alpha)$.
Hence the submultiset of roots of weight $j$ is Galois-stable, so the product
of the corresponding factors $(1-\alpha T)$ lies in $\Q[T]$; with $P_i(0)=1$
this is the sought $P_i$, whose $\ell$-adic extension is $P_{i,\ell}$.
*(ii) Integrality.* Since $A,B\in\Z[T]$ have constant term $1$, the
reciprocal polynomials $A^{\#}(U)=U^{\deg A}A(U^{-1})$ and $B^{\#}$ are
monic with integer coefficients, so every reciprocal root $\alpha$ — the
roots of $A^{\#}$ and $B^{\#}$ are exactly the reciprocal roots of the
$P_{j,\ell}$, by $A=N_\ell$, $B=D_\ell$ — is an algebraic integer. Write
$P_i(T)=\prod_\alpha(1-\alpha T)$, the product over the weight-$i$ stratum;
its coefficients are elementary symmetric functions of algebraic integers,
hence algebraic integers, and rational by (i), hence in $\Z$; so
$P_i\in\Z[T]$. (Equivalently: $P_i\in\Q[T]$ with $P_i(0)=1$ divides the
primitive $A$ or $B$ in $\Q[T]$, so $P_i\in\Z[T]$ by Gauss's lemma. Note
that Frobenius-stability of the lattice $H^{i}(X,\Z_\ell)$ would give only
$\Z_{(\ell)}$-integrality; integrality at $p$ comes from Fatou's lemma, that
is, from the point counts being integers.) Uniqueness is clear from the
determinant formula, and independence of $\ell$ follows because the
presentation $A/B$ and the weight grouping do not mention $\ell$.
*Provenance.* The realization-independence step — that the
factorization is common to all $\ell$ — is the deepest *algebraic*
step of this layer, and the two points above compress seven statements of the
expanded blueprint: `thm-weil-realization-independence` with
`lem-embedding-extension` for the intrinsic weight and the
embedding transport, `prop-galois-weight-strata`,
`prop-galois-weight-strata-integrality` and
`prop-galois-weight-strata-identification` for the Galois stability,
integrality and identification of the strata, and
`prop-integral-recovery` with
`lem-weil-finite-coordinate-detection` for the recovery of the
integral factors. These are pure algebra: no geometric input enters beyond
[sk-prop-rootpurity].

Uses: [sk-def-cohfamily], [sk-def-roots], [sk-prop-rootpurity], [sk-prop-separation], [sk-thm-rationality]
