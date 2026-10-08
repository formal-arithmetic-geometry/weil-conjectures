+++
id = "lem-kun-0f11"
kind = "lemma"
title = "Direct sums and finite cohomological dimension"
order = 1732
uses = ["def-kun-cd", "def-weil-pbc-derived-categories", "def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-direct-image-filtered-colimit", "lemma-weil-pbc-hypercohomology-convergence"]
+++
Let $n\ge1$, and let $f:X\to Y$ be a
quasi-compact and
quasi-separated morphism with $\kuncd(f)<\infty$.

1. **(1)** $Rf_*:D(X_{\Et},\kunZn)\to D(Y_{\Et},\kunZn)$ commutes with
set-indexed direct sums.
1. **(2)** If $X$ is a qcqs scheme with $\kuncd(X)<\infty$, then
$\RGamma(X_{\Et},-):D(X_{\Et},\kunZn)\to D(\kunZn)$ commutes with
set-indexed direct sums.

## Proof

*Step 1 (sheaves).* A set-indexed direct sum of torsion sheaves is
the filtered colimit of its finite partial sums, with split-injective
transition maps, so for every $q$ the canonical map

$$
\bigoplus_iR^qf_*F_i\longrightarrow
R^qf_*\Bigl(\bigoplus_iF_i\Bigr)
$$

is an isomorphism by
[lemma-weil-pbc-direct-image-filtered-colimit] (and the same argument
with $f$ the structure morphism gives the statement for
$\RGamma(X_{\Et},-)$).
*Step 2 (complexes).* For $K_i\in D(X_{\Et},\kunZn)$ ([def-weil-pbc-derived-categories]) the
hypercohomology spectral sequences of
[def-weil-pbc-hypercohomology-filtrations] for the $K_i$ and for
$\bigoplus_iK_i$ have $E_2$-pages $R^pf_*\mathcal H^q(K_i)$
respectively $R^pf_*\mathcal H^q(\bigoplus_iK_i)$, and
$\mathcal H^q(\bigoplus_iK_i)=\bigoplus_i\mathcal H^q(K_i)$, so Step 1
identifies the second $E_2$-page with the direct sum of the first.
The truncation construction of the spectral sequence is compatible with
direct sums, so the spectral sequence of the direct sum is the direct
sum of the spectral sequences; both converge in the half-plane sense of
[lemma-weil-pbc-hypercohomology-convergence] (half-plane, since
$p\ge0$), and a direct sum of separated exhaustive filtrations is
separated and exhaustive. Hence the abutments agree, i.e.

$$
\mathcal H^n\Bigl(Rf_*\bigoplus_iK_i\Bigr)
\cong\bigoplus_i\mathcal H^n(Rf_*K_i)
\qquad(n\in\mathbf Z),
$$

which is the direct-sum statement; the finite-dimensionality hypothesis
$\kuncd(f)<\infty$ of [def-kun-cd] is not needed for the argument
and is retained only to match the classical formulation.
