+++
id = "prop-weil-pbc-reduction-to-projective-line"
kind = "theorem"
title = "Reduction of proper base change to $\\mathbf P^1$"
order = 1204
tags = ["latex:proposition"]
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-projective-embedding", "lem-weil-pbc-reduction-projective-space", "lemma-weil-pbc-cancellation", "lemma-weil-pbc-chow-embedding-over-x", "lemma-weil-pbc-chow-factorization", "lemma-weil-pbc-composition", "lemma-weil-pbc-property-iff-acyclicity", "lemma-weil-pbc-symmetric-product-p1", "lemma-weil-pbc-target-locality", "prop-weil-pbc-composition-stability", "prop-weil-pbc-finite-morphism"]
+++
If every projection $\mathbf P^1_S\to S$ satisfies $\mathsf{PBC}$ for every
base scheme $S$, then every proper morphism satisfies $\mathsf{PBC}$.

## Proof

Use target locality and the Chow factorization. The closed immersion
$X'\hookrightarrow\mathbf P^n_Y$ is proper and finite onto its image, so
finite base change plus composition reduces $X'\to Y$ to
$\mathbf P^n_Y\to Y$. The finite surjective map $\sigma_n$ and cancellation
reduce this projection to $(\mathbf P^1_Y)^n\to Y$. Repeated base change and
composition reduce the product projection to the one-dimensional projection.
Finally cancellation along $\pi$ transfers the property from $X'$ and
$X'\to Y$ to $X\to Y$. Every comparison used is the named exchange map of
Definition [def-weil-pbc-derived-exchange].

## Detailed form

Assume that $\mathbf P^1_S\to S$ satisfies $\mathrm{PBC}$ in the sense of
[def-weil-pbc-property] for every scheme $S$. Then every proper morphism of
schemes satisfies $\mathrm{PBC}$; no finite-presentation hypothesis is
needed, because the Chow factorization [lemma-weil-pbc-chow-factorization]
holds for every proper morphism over an affine base.

## Proof

By [lemma-weil-pbc-target-locality] the assertion is local on the target, so we
work over an affine $Y$, where [lemma-weil-pbc-chow-factorization] supplies $\pi$, $i_Y$, and
the two closed embeddings $i_Y$ and $i_X$ of
[lem-weil-pbc-projective-embedding]. At every use of composition or
cancellation below, first convert all $\mathrm{PBC}$ inputs to $\mathrm{IA}$,
apply the lemma, and convert back. The projective-space projections $\mathbf
P^n_S\to S$ have $\mathrm{PBC}$ by
[lem-weil-pbc-reduction-projective-space]. The Chow map factors as $\pi=q_X\circ
i_X$, where $i_X$ is finite and hence has $\mathrm{PBC}$ by
[prop-weil-pbc-finite-morphism], and $q_X:\mathbf P^n_X\to X$ has
$\mathrm{PBC}$; composition by [prop-weil-pbc-composition-stability] gives
$\mathrm{PBC}$ for $\pi$. Likewise $f\pi=q_Y\circ i_Y$ has $\mathrm{PBC}$.
Since $\pi$ is proper and surjective, [lemma-weil-pbc-cancellation] applied to
$\pi$ and $f$ gives $\mathrm{PBC}$ for $f$.
