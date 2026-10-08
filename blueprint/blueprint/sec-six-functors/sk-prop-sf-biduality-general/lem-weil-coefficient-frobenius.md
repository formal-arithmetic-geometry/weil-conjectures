+++
id = "lem-weil-coefficient-frobenius"
kind = "lemma"
title = "Coefficient biduality at finite and integral stages"
order = 2120
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-finite-torsion-constructibility"]
+++
For the coefficient stages of
[def-weil-finite-torsion-constructibility] and
[def-weil-derived-complete-integral-detailed], the following distinctions hold.

1. If $\Lambda=A_{E,n},E$, or
$\overline{\mathbf Q}_\ell$, then $\Lambda$ is self-injective and
quasi-Frobenius. Ordinary duality $\operatorname{Hom}_\Lambda(-,\Lambda)$
is exact, preserves finite modules, and for every finite
$\Lambda$-module $M$ the evaluation map
$$
M\longrightarrow
\operatorname{Hom}_\Lambda\bigl(\operatorname{Hom}_\Lambda(M,\Lambda),\Lambda\bigr)
$$
is an isomorphism. Consequently derived coefficient duality is an
anti-equivalence on bounded complexes with finite cohomology.
1. The discrete valuation ring $R=\mathcal O_E$ is not
quasi-Frobenius. Ordinary evaluation is an isomorphism for finite
projective $R$-modules, but not for all finite $R$-modules.
Every $K\in D^b(R)$ with finite cohomology is perfect, and the
*derived* evaluation
$$
K\longrightarrow
R\operatorname{Hom}_R\bigl(R\operatorname{Hom}_R(K,R),R\bigr)
$$
is an isomorphism.
1. More generally, derived evaluation into the coefficient double dual
is an isomorphism for every perfect complex over any ring. In particular,
the finite-Tor point case does not require self-injectivity of the
coefficient ring.

## Proof

The field cases are finite-dimensional vector-space duality. For
$A=A_{E,n}=\mathcal O_E/\varpi_E^n$, every ideal is
$\varpi^iA$. A homomorphism $u:\varpi^iA\to A$ satisfies
$\varpi^{n-i}u(\varpi^i)=0$, hence
$u(\varpi^i)\in\varpi^iA$. Write
$u(\varpi^i)=\varpi^ib$; multiplication by $b$ extends $u$ to
$A$. Baer's criterion, Stacks Project,
[Tag 0AVF](https://stacks.math.columbia.edu/tag/0AVF), now gives
self-injectivity. Since $A$ is Artinian, it is quasi-Frobenius.
A finite $A$-module is a finite direct sum of cyclic modules
$A/\varpi^i$, so it suffices to check evaluation on these. A functional
$A/\varpi^i\to A$ is determined by its value at $1$, which lies in
$\operatorname{Ann}_A(\varpi^i)=\varpi^{n-i}A/\varpi^n$, so that

$$
\operatorname{Hom}_A(A/\varpi^i,A)\cong\varpi^{n-i}A/\varpi^n
\cong A/\varpi^i ;
$$

the evaluation map at $1$ is a generator of the double dual, hence an
isomorphism. Exactness of $\operatorname{Hom}_A(-,A)$ and bounded
truncation give derived biduality for bounded finite cohomology.

Over $R=\mathcal O_E$, the finite module $T=R/\varpi_E R$ is
nonzero but $\operatorname{Hom}_R(T,R)=0$. In particular ordinary
duality is not exact: applying it to
$0\to R\xrightarrow{\varpi_E}R\to T\to0$ leaves the nonsurjective
map $R\xrightarrow{\varpi_E}R$. Thus $R$ is not self-injective.
It is a regular ring, so bounded complexes with finite cohomology are
perfect by Stacks Project,
[Tag 066Z](https://stacks.math.columbia.edu/tag/066Z).
For a perfect complex over any ring, a bounded finite projective model
computes its derived dual, and termwise evaluation computes the derived
double dual; this is Stacks Project,
[Tag 07VI](https://stacks.math.columbia.edu/tag/07VI).
It proves both the integral assertion and the last clause.
