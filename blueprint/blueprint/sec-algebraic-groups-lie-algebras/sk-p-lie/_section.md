+++
id = "sk-p-lie"
kind = "section"
title = "Lie algebra structure"
order = 2468
uses = ["sk-d-lie"]
lean = ["LieAlgebra.hasCentralRadical_of_isFaithful", "LieAlgebra.center_sup_derivedSeries_eq_top"]
+++
*Proposition (sketch).*

A finite-dimensional Lie algebra $L$ over $k$ admitting
a faithful semisimple representation has central radical and satisfies

$$
\rad L=Z(L),\qquad L=Z(L)+[L,L].
$$

The plus sign denotes a sum of subspaces.

## Proof

Decompose the representation as in [sk-d-lie], and let $L_i$ be the
image on a simple summand. The image of $\rad L$ lies in $\rad L_i$,
which is central by the irreducible characteristic-zero Lie theorem,
available in Mathlib as
`LieAlgebra.hasCentralRadical_and_of_isIrreducible_of_isFaithful`
(its triangularizability hypothesis being supplied over the algebraically
closed $k$ by `LieModule.instIsTriangularizableOfIsAlgClosed`);
the auxiliary facts that surjective Lie maps carry solvable ideals to
solvable ideals and that the radical is solvable and contains every
solvable ideal are `LieHom.isSolvable_range`,
`LieAlgebra.radicalIsSolvable` and
`LieIdeal.solvable_iff_le_radical`. Thus $[L,\rad L]$ acts as zero
on every summand; faithfulness makes it zero in $L$. The center is an
abelian ideal, so it lies in the radical, giving equality.
The quotient $L/Z(L)$ has zero radical: the inverse image of a solvable
ideal is solvable, since its kernel is central. Cartan's criterion,
available in Mathlib as
`LieAlgebra.HasTrivialRadical.instIsKilling`, makes its Killing
form nondegenerate; invariance of that form puts the orthogonal complement
of the derived algebra inside the center, which is zero, so the quotient is
perfect. Lift an expression of each quotient class as a
sum of brackets; the difference from these lifted brackets lies in
$Z(L)$. This proves the sum formula, including the zero-dimensional case.

Uses: [sk-d-lie]
