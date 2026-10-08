+++
id = "lem-pc-finite-linear-avoidance"
kind = "lemma"
title = "Avoiding finitely many linear subspaces"
order = 647
+++
Let $k$ be an infinite field, let $V$ be a finite-dimensional
$k$-vector space, and let $W_1,\ldots,W_s$ be proper linear
subspaces. Then $V\ne\bigcup_{j=1}^s W_j$.

## Proof

For each $j$, extend a basis of $W_j$ to one of $V$ and take a
nonzero coordinate functional $\lambda_j$ vanishing on $W_j$.
Their product is a nonzero polynomial on $V$, since the polynomial
ring over $k$ is a domain. A nonzero polynomial over an infinite
field cannot vanish at every point of affine space: in one variable
it has at most its degree many roots; in several variables first
choose values at which one nonzero coefficient polynomial is nonzero,
by induction, and then choose the last coordinate avoiding the
finitely many roots of the resulting one-variable polynomial.
A point where $\prod_j\lambda_j$ does not vanish belongs to none
of the $W_j$. For $s=0$ any vector suffices.
