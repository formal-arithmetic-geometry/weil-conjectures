+++
id = "lem-weil-pbc-symmetric-product-properties"
kind = "lemma"
title = "No common zero and permutation invariance"
order = 1200
uses = ["def-weil-pbc-symmetric-product-morphism"]
+++
The polynomials $F_0,\dots,F_n$ of [def-weil-pbc-symmetric-product-morphism]
have no common zero on $(\mathbf P^1_S)^n$ and are invariant under the action
of the symmetric group $S_n$. Hence
[def-weil-pbc-symmetric-product-morphism] gives an $S_n$-invariant morphism

$$
 \sigma_n:(\mathbf P^1_S)^n\longrightarrow\mathbf P^n_S.
$$

## Proof

A common zero of all $F_j$ would make the product $\prod_{i=1}^n(x_it+y_i)$
the zero polynomial in $t$, forcing some pair $(x_i,y_i)$ to vanish, which is
impossible in $\mathbf P^1$. Permuting the factors fixes every $F_j$, so
$\sigma_n$ is $S_n$-invariant.
