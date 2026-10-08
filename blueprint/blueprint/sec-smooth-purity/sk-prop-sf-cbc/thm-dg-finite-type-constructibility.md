+++
id = "thm-dg-finite-type-constructibility"
kind = "theorem"
title = "Bounded constructibility of every finite-type direct image"
order = 1641
uses = ["cor-fin-deligne-open-finite-coefficients", "def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lem-fin-proper-bounded-constructible", "lem-weil-derived-direct-image-composition", "lem-weil-pbc-grothendieck-spectral-sequence", "sbc-def-coefficient-conventions", "thm-constructible-serre"]
+++
Let $f:X\to Y$ be a morphism between finite-type schemes over
a field $k$, and let $A$ be a finite ring annihilated by an
integer invertible in $k$. Then

$$
Rf_*:D^b_c(X,A)\longrightarrow D^b_c(Y,A)
$$

is defined on the ordinary derived categories. The morphism
$f$ need not be separated.
The notation refers to bounded constructible complexes.

## Proof

The assertion is local on $Y$. Choose a finite affine cover
of $Y$, prove it on each member, and take the finite union of
the resulting cohomological ranges. We may therefore assume
$Y$ affine. Cover $X$ by finitely many affine opens
$X_1,\ldots,X_r$. For each nonempty subset
$I\subset\{1,\ldots,r\}$, the intersection
$X_I=\bigcap_{i\in I}X_i$ is a quasi-compact open of the affine
scheme $X_i$ for any $i\in I$. It need not be affine.
The finite-type morphism $X_i\to Y$ admits a closed embedding
in $\mathbf A^m_Y$; hence $X_I$ is locally closed in
$\mathbf P^m_Y$. In its scheme-theoretic closure
$\overline X_I$, it is open and dense. We obtain a factorization

$$
f_I:X_I\xrightarrow{j_I}\overline X_I
\xrightarrow{p_I}Y
$$

with $j_I$ open and $p_I$ projective. The two preceding
results [cor-fin-deligne-open-finite-coefficients], [lem-fin-proper-bounded-constructible]
prove bounded constructibility of
$Rf_{I,*}K|_{X_I}=Rp_{I,*}Rj_{I,*}K|_{X_I}$.
Composition of the derived direct images is
[lem-weil-derived-direct-image-composition] (item (5)); on cohomology
sheaves it is
[lem-weil-pbc-grothendieck-spectral-sequence].

For completeness, use the finite alternating Cech resolution
of the open cover. In degree $p$ it has the direct sum over
strictly increasing index sets $i_0<\cdots<i_p$, so
$0\leq p\leq r-1$. Its augmented rows are exact: near any
point of $X$, choose a member of the cover containing that
point and contract the augmented alternating complex by inserting
its index. Apply this to an injective resolution of $K$.
Restriction to an open preserves injectives because its left
adjoint, extension by zero in
[def-weil-pbc-extension-by-zero], is exact. Thus after
applying $f_*$ the double complex gives

$$
E_1^{p,q}=\bigoplus_{|I|=p+1}
\mathcal H^q(Rf_{I,*}K|_{X_I})
\ \Longrightarrow\ \mathcal H^{p+q}(Rf_*K).
$$

There are only finitely many subsets $I$, and each corresponding
direct image has a finite range already proved above. Hence this
spectral sequence lies in a bounded rectangle. Every term on
every page is constructible by kernels and cokernels, and each
abutment has a finite constructible filtration, using
[thm-constructible-serre]. Outside the finite sum
of the two ranges the abutment vanishes. This proves the theorem
without an unbounded Cech argument, an affine-intersection
assumption, or a closed-base-change identification for $Rj_*$.
