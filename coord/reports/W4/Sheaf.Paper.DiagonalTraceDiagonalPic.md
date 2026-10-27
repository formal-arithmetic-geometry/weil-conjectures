## What changed

Replaced the proof of
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_diagonalPic_factorization`
without changing its signature or its public import. Added two private proof imports:
`Sheaf.AlgebraicGeometry.FiniteP1DiagonalPicard` and
`Sheaf.AlgebraicGeometry.ProjectiveLineAutomorphismHyperplane`.

The diagonal-specific calculation is already proved by
`AlgebraicGeometry.Etale.finiteP1_diagonal_picard`. A private helper applies it
with the existing Cartier proof, for both Boolean projection charts. The main proof
compares the canonical chart c with the supplied model e. Their composite is an
automorphism g of the standard relative projective line. If g pulls the hyperplane
class back to q*B times H, the base coefficient needed in the original statement is
H_Y times B inverse. The proof uses the existing skeleton representative of that
Picard class, pulls the proposed equality along c, substitutes the two formulas,
and cancels in the Picard group. Pullback along c is injective by its inverse.
All these transport and cancellation steps are actual Lean proofs.
The large ProjectiveSpace definition is locally irreducible during the proof;
this changes no interface or downstream unfolding.

Validation: lcompile.py --all compiled both modules. Temporary profiler options
were removed before submitting the final packet; deliver3.py performs the final
compile and preflight checks on that version.

The new module isolates only the generic automorphism/hyperplane step from EGA II
Remark 4.2.7. It mentions neither the product of two projective lines nor the diagonal,
its ideal, Chern classes, trace, or integration. Its source and complete proof in words
are included. The item's DAG proof now records the canonical calculation followed by
this generic model change and the proved Picard algebra.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_diagonalPic_factorization`
(node `lem-sfb-diagonal-trace-diagonal-pic`). No `sorry` remains in the item module.

Added one strictly smaller remaining hole:
`AlgebraicGeometry.ProjectiveLine.automorphism_hyperplane`
(node `lem-sfb-projective-line-automorphism-hyperplane`), in the new module
`Sheaf.AlgebraicGeometry.ProjectiveLineAutomorphismHyperplane`.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The entire diagonal divisor calculation is discharged using an existing proved
result; only changing the hyperplane line under a relative automorphism remains.
No definitions, instances, or existing statement signatures were changed.

## No longer needed

No existing import was removed, and no existing module is claimed pruned.

The item no longer directly uses
`lem-sfb-projective-bundle-picard-classification`: only the new generic
hyperplane lemma needs its classification argument. It no longer directly uses
`lem-sp-p1-diagonal-local-ideal`: that calculation is already encapsulated in the
proved `lem-sp-finite-p1-diagonal-picard`. Both dependencies remain necessary
transitively, and their modules and declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan did not expose the concrete change-of-model bridge. The
classification declaration is for an abstract relative Proj of a symmetric algebra;
it is not directly an equality of Picard classes on the concrete standard
`ProjectiveLine`. The generic projective-frames node also discusses this bridge,
but it currently has no Lean attachment. The new node states only its rank-two
hyperplane clause; it does not restate the assigned diagonal theorem.

Searches through msearch.py (Lean Finder, Loogle and grep), plus local source searches,
found no existing declaration of that clause. Reading EGA II printed page 75
confirmed the degree-one assertion for projective-bundle isomorphisms. The
arbitrary-base argument uses the already stated Picard classification and its
finite-presentation-descent extension. Empty, disconnected and nonreduced bases
are included; no additional hypothesis is introduced.

## New nodes

`lem-sfb-projective-line-automorphism-hyperplane` states that a relative
projective-line automorphism fixes the standard hyperplane Picard class modulo
pullbacks of base lines. It is exactly the model-change part of the original
argument. Its proof plan applies projective-bundle Picard classification, proves
the fibre degree is +1 by inverse Picard maps and the vanishing of sections of
O(-1), and passes the resulting tensor isomorphism to Picard classes. Its three
proof dependencies already have Lean declarations. There are no change records
because no existing interface was altered.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
