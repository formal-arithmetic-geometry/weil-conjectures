+++
id = "lem-pc-genus-base-change"
kind = "lemma"
title = "The genus is invariant under base change"
order = 737
uses = ["def-pc-base-change", "def-pc-smooth-projective-curve", "def-sc-curves", "lem-pc-proper-base-change", "lem-sc-flat-base-change-coherent"]
+++
Let $k$ be a field, $X$ a
smooth projective curve over
$k$ which is geometrically irreducible with $H^0(X,\mathcal{O}_X)=k$, and let
$K/k$ be a field extension. Then
$g(X_K)=\dim_KH^1(X_K,\mathcal{O}_{X_K})=g(X)$. If $k$ is separably closed (or
more generally $H^0(X,\mathcal{O}_X)=k$), this applies in particular when
$X_K$ is a connected curve in the sense of [def-sc-curves].

## Proof

The base change $X_K=X\times_{\operatorname{Spec} k}\operatorname{Spec} K$ is proper over $K$
(base change of proper [lem-pc-proper-base-change]), and the
structure morphism $X\to\operatorname{Spec} k$ is proper, so by
[lem-sc-flat-base-change-coherent] (the affine/flat base change
case, already decomposed in file 06, applied with the flat $k$-algebra
$K$):

$$
H^1(X_K,\mathcal{O}_{X_K})\cong H^1(X,\mathcal{O}_X)\otimes_kK,
$$

whence $\dim_KH^1(X_K,\mathcal{O}_{X_K})=\dim_kH^1(X,\mathcal{O}_X)=g(X)$.
