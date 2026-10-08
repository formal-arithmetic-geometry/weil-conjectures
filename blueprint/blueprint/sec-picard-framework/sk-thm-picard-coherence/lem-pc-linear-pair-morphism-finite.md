+++
id = "lem-pc-linear-pair-morphism-finite"
kind = "lemma"
title = "Finiteness of the morphism from two linear forms"
order = 653
uses = ["def-pc-linear-pair-morphism", "def-pc-morphism-conventions", "def-pc-proj", "def-pc-standard-graded-algebra", "lem-pc-linear-pair-graded-finite", "lem-pc-linear-pair-morphism-gluing"]
+++
In the setup of the morphism
$\pi_{l_0,l_1}$, that morphism is
finite.

## Proof

Choose $N$ as in [lem-pc-linear-pair-graded-finite].
Every $S_d$ is finite-dimensional: it is spanned by the finitely
many degree-$d$ monomials in the generators of
[def-pc-standard-graded-algebra].
Take the union of bases of $S_0,\ldots,S_{N-1}$, and denote
its elements by $g_1,\ldots,g_r$ with degrees $d_j$.
Induction on $n$, using $S_n=l_0S_{n-1}+l_1S_{n-1}$ for
$n\ge N$, expresses each $s\in S_n$ as

$$
s=\sum_{j=1}^r F_j(l_0,l_1)g_j,
$$

where each $F_j$ is homogeneous of degree $n-d_j$ (and is zero
if that degree is negative). This proves finite generation of
$S$ as a module over the image of $k[T_0,T_1]\to S$,
$T_i\mapsto l_i$; injectivity of this ring map is unnecessary.

The inverse image of $D_+(T_i)\subset\mathbf P^1_k$ is exactly
$D_+(l_i)$ by [def-pc-linear-pair-morphism] (the morphism is the
one glued in [lem-pc-linear-pair-morphism-gluing]). It is affine
with coordinate ring $S_{(l_i)}$ by [def-pc-proj].
For $i=0$, divide the displayed homogeneous expression by $l_0^n$:

$$
\frac{s}{l_0^n}
=\sum_j F_j(1,l_1/l_0)\frac{g_j}{l_0^{d_j}}.
$$

Thus the finitely many $g_j/l_0^{d_j}$ generate $S_{(l_0)}$
as a module over $k[t]$, with $t$ acting by $l_1/l_0$.
The identical computation with $l_1$ proves finite generation
over $k[t^{-1}]$ on the other chart.
The affine-open definition of a finite morphism in
[def-pc-morphism-conventions] now proves the assertion.
