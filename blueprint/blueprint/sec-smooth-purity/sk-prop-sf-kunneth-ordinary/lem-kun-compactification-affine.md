+++
id = "lem-kun-compactification-affine"
kind = "lemma"
title = "Compactification of an affine scheme"
order = 1746
uses = ["def-kun-dimension", "def-kun-projective", "def-weil-pbc-derived-categories", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be an affine scheme of finite type over a field $K$. There
is an open dense immersion $X\to\bar X$ with $\bar X$ projective
over $K$ (choose a closed immersion $X\hookrightarrow\mathbf A^n_K$, take the scheme-theoretic closure in $\mathbf P^n_K$); one
has $\kundim\bar X=\kundim X$.

## Proof

Write $X=\Spec(B)$ with $B$ a finitely generated $K$-algebra,
fix a surjection $K[T_1,\ldots,T_n]\twoheadrightarrow B$, giving a
closed immersion $X\hookrightarrow\mathbf A^n_K$ ($\mathbf A^n_K=\Spec(K[T_1,\ldots,T_n])$); the open immersion
$\mathbf A^n_K\hookrightarrow\mathbf P^n_K$ identifies the
complement of the hyperplane at infinity. Let $\bar X$ be the
scheme-theoretic closure of $X$ in $\mathbf P^n_K$; then
$\bar X$ is a closed subscheme of $\mathbf P^n_K$, hence
projective over $K$ by [def-kun-projective], and $X= \bar X\cap\mathbf A^n_K$ is open dense in $\bar X$. The generic
points of $\bar X$ lie in the open subset $X$, so
$\kundim\bar X=\kundim X$ by
[def-kun-dimension].
