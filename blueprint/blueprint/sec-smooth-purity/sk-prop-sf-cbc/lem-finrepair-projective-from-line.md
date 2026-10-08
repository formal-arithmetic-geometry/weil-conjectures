+++
id = "lem-finrepair-projective-from-line"
kind = "lemma"
title = "Projective constructibility from projective-line constructibility"
order = 1600
uses = ["def-finrepair-property-c", "def-weil-pbc-scheme-conventions", "lem-fin-closed-immersion", "lem-fin-symmetric-product-finite", "lem-finrepair-composition-c", "lem-finrepair-finite-surjection-cancellation"]
+++
Suppose $\mathcal C(\mathbf P^1_T\to T)$ holds for every
finite-type $k$-scheme $T$. Then $\mathcal C(f)$ holds for
every projective morphism $f:X\to S$ between finite-type
$k$-schemes, using the conventions of
[def-finrepair-property-c], [def-weil-pbc-scheme-conventions].

## Proof

Work locally on $S$, choosing a closed immersion
$X\hookrightarrow\mathbf P^n_S$ as in the projective convention of
[def-weil-pbc-scheme-conventions]. Restriction to a target open
commutes with direct image and its derived functors: on an etale
object over that open the two section functors are the same, and
restriction has an exact extension-by-zero left adjoint and hence
preserves injectives. Constructibility glues over a finite open
cover by combining the finite stratifications. This justifies the
target localization.

The product $(\mathbf P^1_S)^n\to S$ is a composite of
projective-line projections over the successive finite-type bases.
The hypothesis and [lem-finrepair-composition-c] therefore give
constructibility for this product projection.
The explicitly constructed symmetric-product map

$$
\sigma_n:(\mathbf P^1_S)^n\longrightarrow\mathbf P^n_S
$$

is finite and surjective by [lem-fin-symmetric-product-finite].
Consequently [lem-finrepair-finite-surjection-cancellation]
proves constructibility for $\mathbf P^n_S\to S$.
For $n=0$ it is the identity and the assertion is immediate.
Finally, the closed immersion $X\hookrightarrow\mathbf P^n_S$
has exact constructibility-preserving direct image by
[lem-fin-closed-immersion]. Compose with the projection using
[lem-finrepair-composition-c]. This proves the assertion.
