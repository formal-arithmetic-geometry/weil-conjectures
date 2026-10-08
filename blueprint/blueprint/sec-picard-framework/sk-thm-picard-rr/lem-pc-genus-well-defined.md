+++
id = "lem-pc-genus-well-defined"
kind = "lemma"
title = "Well-definedness of the genus"
order = 736
uses = ["def-pc-morphism-conventions", "lem-pc-curve-coherent-finiteness", "lem-sc-flat-base-change-coherent"]
+++
Let $k$ be a field and $X$ a smooth projective curve over $k$ which is
geometrically irreducible. Then
$\dim_kH^1(X,\mathcal{O}_X)<\infty$.

## Proof

After extending scalars to an algebraic closure $\bar k/k$, the curve
$X_{\bar k}$ is smooth projective and geometrically irreducible. Hence
[lem-pc-curve-coherent-finiteness], applied to
$\mathcal O_{X_{\bar k}}$, makes $H^1(X_{\bar k},\mathcal O)$ finite-dimensional
over $\bar k$. The base-change isomorphism of
[lem-sc-flat-base-change-coherent] identifies this space with
$H^1(X,\mathcal O_X)\otimes_k\bar k$. A vector space whose scalar extension
is finite-dimensional is already finite-dimensional: every linearly
independent finite subset remains independent after a field extension,
so its cardinality is bounded by the dimension after extension.
This proves the claim over $k$.
