+++
id = "lem-fin-projective-curve-betti-cardinalities"
kind = "lemma"
title = "Betti cardinalities in a smooth projective curve family"
order = 1610
uses = ["def-pc-projective-morphism", "def-sbc-smooth-morphisms", "def-sc-curves", "def-sc-genus", "def-sc-mu-trivialization", "def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "lem-fin-projective-flat-coherent-ranks", "lem-sc-cohomological-dimension", "lem-sc-global-functions", "thm-sc-proper-cohomology"]
+++
Let $S$ be Noetherian
and let $f:X\to S$ be
smooth and
projective, with geometric
fibres of pure dimension one. Fix a prime $\ell$ invertible on $S$.
Write $c_s$ for the number of connected components of the
smooth proper curve $X_{\bar s}$, and
$g_s=\sum_D g(D)$ for the sum of the
genera over its connected components.
Then the etale cohomology
cardinalities are

$$
|H^r(X_{\bar s},\mathbf F_\ell)|=
\begin{cases}
\ell^{c_s},&r=0,2,\\
\ell^{2g_s},&r=1,\\
1,&r>2,
\end{cases}
$$

and each of these functions of $s$ is constructible.

## Proof

A smooth geometric fibre is regular. Its finitely many irreducible
components are disjoint, since a regular local ring is a domain.
Thus its connected components are integral smooth proper curves.
By [lem-sc-global-functions], each contributes one copy of
$\kappa(\bar s)$ to $H^0(\mathcal O)$, and by
[def-sc-genus] its genus is its $H^1(\mathcal O)$ dimension.
Cohomology on a finite disjoint union is the direct sum of the
component cohomologies, so

$$
c_s=h^0(X_{\bar s},\mathcal O),\qquad
g_s=h^1(X_{\bar s},\mathcal O).
$$

Smoothness includes flatness by [def-sbc-smooth-morphisms];
apply [lem-fin-projective-flat-coherent-ranks] to
$\mathcal G=\mathcal O_X$. It proves constructibility of both
functions, without assuming all components have the same genus.
The twist trivialization of [def-sc-mu-trivialization] and the
curve computation [thm-sc-proper-cohomology] give ranks
$1,2g(D),1$ in degrees $0,1,2$ on each component.
Vanishing above degree two is
[lem-sc-cohomological-dimension]. Sum over components and
take cardinalities to obtain the formula and its constructibility.
