+++
id = "lem-rp-exterior-reality"
kind = "lemma"
title = "Reality of exterior powers"
order = 2600
uses = ["def-real-weil-representation-operations", "def-wf-iota-real", "def-wf-weil-category", "p-linear-spectra", "p-linear-triangular"]
+++
If $\mathcal G_0$ is an $\iota$-real lisse Weil sheaf, then
$\bigwedge^r\mathcal G_0$ (the exterior power of
[def-real-weil-representation-operations]) is $\iota$-real for every
$0\le r\le\rank(\mathcal G_0)$.

## Proof

At a closed point $x$, write the complex eigenvalues of $F_x$ on
$\mathcal G_{0,\bar x}$ as $\lambda_1,\ldots,\lambda_s$, with
multiplicity. After triangularizing $F_x$ ([p-linear-triangular]), the eigenvalues on
$\bigwedge^r\mathcal G_{0,\bar x}$ are the products
$\lambda_{i_1}\cdots\lambda_{i_r}$ over $r$-element subsets of
$\{1,\ldots,s\}$, counted with multiplicity ([p-linear-spectra]). Complex conjugation
permutes the original multiset by $\iota$-reality, and therefore
permutes this product multiset. The local characteristic polynomial of
$\bigwedge^r\mathcal G_0$ consequently has real coefficients.
This is exactly $\iota$-reality in the sense of
[def-wf-iota-real].
