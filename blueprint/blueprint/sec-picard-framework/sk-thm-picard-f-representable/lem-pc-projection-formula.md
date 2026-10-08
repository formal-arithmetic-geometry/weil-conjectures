+++
id = "lem-pc-projection-formula"
kind = "lemma"
title = "The projection formula"
order = 829
uses = ["def-pc-base-change", "def-pc-derived-category", "def-pc-derived-direct-image", "def-sc-invertible-module"]
+++
Let $f:X\to Y$ be a quasi-compact, quasi-separated morphism of schemes.
For $E\in D_{\text{QCoh}}(\mathcal{O}_X)$ and $K\in D_{\text{QCoh}}(\mathcal{O}_Y)$ the
canonical map

$$
Rf_*(E)\otimes_{\mathcal{O}_Y}^{\mathbb L}K\;\longrightarrow\;
Rf_*(E\otimes_{\mathcal{O}_X}^{\mathbb L}Lf^*K)
$$

is an isomorphism; in particular, for an invertible
$\mathcal{O}_Y$-module $\mathcal{N}$,
$Rf_*(E)\otimes\mathcal{N}\cong Rf_*(E\otimes f^*\mathcal{N})$.

## Proof

The map of the statement (defined in Cohomology, Equation 20.54.2.1) is
natural in $E$ and $K$, so: (1) the assertion is local in $Y$: if
$Y=\bigcup_{i\in I}V_i$ is an open covering, the objects and the map
restrict to the open sets (the derived functors localize: $Rf_*$ and
$\otimes^{\mathbb L}$ are computed on the open subschemes and the
restriction maps are the restrictions of the canonical maps), and
$D_{\text{QCoh}}$-identifications can be checked on an open cover; so
we may assume $Y$ affine, $Y=\operatorname{Spec}(A)$. (2) For the affine $Y$, the
functor $D_{\text{QCoh}}(\mathcal{O}_Y)\to D(A)$ (global sections, with the
standard equivalence $D_{\text{QCoh}}(\mathcal{O}_Y)\cong D(A)$, cf. Derived
Categories of Schemes, Lemma 36.3.5, Section 36.3, chapter Tag
[08CU](https://stacks.math.columbia.edu/tag/08CU)) identifies both
sides: the case $K=A[k]$ is the statement
$Rf_*(E[k])\cong Rf_*(E)[k]$ (the shift: clear); an object $K$ is a
retract of a complex which is built up by direct sums and distinguished
triangles from shifts $A[k]$ (the standard dissage: the functors
$Lf^*$, $\otimes^{\mathbb L}$, $Rf_*$ preserve direct sums and exact
triangles, so the property "$P(K)$ holds" is stable under triangles and
passes to direct sums, and the class of $K$'s with $P(K)$ contains
$A[k]$ and is closed under the two operations and retracts; the
"the standard: every object of $D(A)$ is obtained from a complex of
free modules whose terms are sums..., by the inductive tower of
truncations" – the classical proof of the cofiber-type generation:
the full subcategory generated is $D(A)$: the truncations argument
reduces to the bounded case and the "bounded complexes are filtered by
the shifts of their quotients $M^i$'-type (the exact triangles
$M^{[p,q]}\to M^{[p,q+1]}\to M^{q+1}[-q-1]\to$" with
$M^q$ free after a resolution; this is the standard identical argument
that one uses for the derived functors' basic properties, as in the
proof of Lemma 36.22.1, Tag
[08EU](https://stacks.math.columbia.edu/tag/08EU)). Hence $P(K)$
holds for all $K$. (3) The last statement: for an invertible $\mathcal{N}$,
$\mathcal{N}$ as an object of $D_{\text{QCoh}}$ and the natural map
$Rf_*E\otimes\mathcal{N}\to Rf_*(E\otimes f^*\mathcal{N})$ is the
$\otimes^{\mathbb L}$-statement specialized to $K=\mathcal{N}[0]$ (with
$\otimes^{\mathbb L}\mathcal{N}=\otimes\mathcal{N}$ since $\mathcal{N}$ is locally free, and
$Lf^*\mathcal{N}=f^*\mathcal{N}$).
