+++
id = "lem-weil-pbc-reduction-projective-space"
kind = "lemma"
title = "Reduction of projective space to products of lines"
order = 1203
uses = ["def-weil-pbc-property", "def-weil-pbc-symmetric-product-morphism", "lem-weil-pbc-symmetric-product-finite", "lem-weil-pbc-symmetric-product-surjective", "lemma-weil-pbc-cancellation", "prop-weil-pbc-composition-stability", "prop-weil-pbc-finite-morphism"]
+++
Assume that for every scheme $S$ the projection $\mathbf P^1_S\to S$ satisfies
$\mathrm{PBC}$ in the sense of [def-weil-pbc-property]. Then, for every scheme
$T$ and every $n\geq0$, the product projection $(\mathbf P^1_T)^n\to T$
satisfies $\mathrm{PBC}$ by repeated base change and composition (over the
successive bases $T,\mathbf P^1_T,\dots$), and $\mathbf P^n_T\to T$ satisfies
$\mathrm{PBC}$ by cancellation along $\sigma_n$.

## Proof

The product projection $(\mathbf P^1_T)^n\to T$ is a composite of $n$
projective-line projections over successive bases, so it has $\mathrm{PBC}$ by
[prop-weil-pbc-composition-stability] applied stepwise. The morphism
$\sigma_n$ is finite by [lem-weil-pbc-symmetric-product-finite], hence has
$\mathrm{PBC}$ by [prop-weil-pbc-finite-morphism], and is surjective by
[lem-weil-pbc-symmetric-product-surjective]. Since $(\mathbf
P^1_T)^n\to\mathbf P^n_T\to T$ composes to the product projection,
[lemma-weil-pbc-cancellation] gives $\mathrm{PBC}$ for $\mathbf P^n_T\to T$.
