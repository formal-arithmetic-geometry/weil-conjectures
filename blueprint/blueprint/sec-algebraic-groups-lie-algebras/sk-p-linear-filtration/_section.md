+++
id = "sk-p-linear-filtration"
kind = "section"
title = "Characteristic polynomials along a filtration"
order = 2548
uses = ["sk-d-linear"]
lean = ["LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ", "Module.End.hasEigenvalue_of_subquotient"]
+++
*Proposition (sketch).*

Let $f$ be an endomorphism of a finite-dimensional
$k$-space $V$ preserving a filtration with graded
pieces $\mathrm{gr}_j$. Then

$$
\det(1-Tf\mid V)=\prod_j\det\bigl(1-Tf\mid\mathrm{gr}_j\bigr).
$$

In particular the eigenvalues of $f$ on any subquotient occur among those
on $V$, with multiplicity; so a scalar acting on a nonzero invariant
subquotient is an eigenvalue on the ambient space.
lem:filtration-constituent;lem:scalar-subquotient-eigenvalue

## Proof

It is enough to treat one invariant subspace and iterate along the
filtration. For $S\subseteq V$ with $f(S)\subseteq S$, choose a basis of
$S$ and extend it to $V$; over the polynomial ring $k[T]$ the matrix of
$1-Tf$ is then block upper triangular, with diagonal blocks those of
$1-Tf$ on $S$ and on $V/S$, so its determinant is the product of the two
block determinants. Induction on the length of the filtration gives the
displayed formula. A subquotient $S/U$ sits in the flag
$0\subseteq U\subseteq S\subseteq V$, so $\det(1-Tf\mid S/U)$ divides
$\det(1-Tf\mid V)$, which is the statement about eigenvalues with
multiplicity. If $f$ acts on $S/U\ne0$ by the scalar $c$, apply the same
factorization to $B=f-c$: the middle factor is the determinant of the zero
map on a space of positive dimension, hence zero, so
$\det(f-c\operatorname{id}_V)=0$ and $c$ is an eigenvalue on $V$.
The determinant factorization along an invariant subspace is Mathlib's
`LinearMap.det_eq_det_mul_det`, in matrix form
`Matrix.charpoly_fromBlocks_zero`$_{12}$; what is not available
is the statement above, Mathlib having only the direct-sum case
`LinearMap.charpoly_prodMap`.

Uses: [sk-d-linear]
