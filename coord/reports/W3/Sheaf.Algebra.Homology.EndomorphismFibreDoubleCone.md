## What changed

Filled `CochainComplex.EndomorphismFibreDoubleCone.exists_interchange` in
`Sheaf.Algebra.Homology.EndomorphismFibreDoubleCone`. The proof constructs the signed
four-coordinate permutation using Mathlib's cone and cocone inclusions. Private
projection lemmas establish the differential formula, inverse, naturality, triangle
identities, and compatibility with the zero-second-coordinate augmentations.
All public statements and definitions are unchanged. No imports were added.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.EndomorphismFibreDoubleCone.exists_interchange`
(node `lem-pe-endomorphism-fibre-double-cone`). No holes added or split off; no
`sorry` remains in the delivered module. All private helper lemmas are proved.
Remote single-file compilation passed cleanly in 7.4 seconds, with no warnings.
The delivery tool also runs its required axiom probe and preflight before pushing.

## No longer needed

None. The argument uses the finite biproduct and mapping cone/shift APIs of
`def-sp-abelian` and `def-weil-abstract-derived-category`, exactly as in the DAG.
The three original public imports remain necessary for the public interface.
The searches by LeanFinder, Loogle, and grep found the cone map and shift APIs,
but no existing theorem with the required strict four-coordinate, naturality,
triangle-boundary, and augmentation identities. The related signed-fibre cone
construction has values in abelian groups and does not apply to an arbitrary
abelian category without additional comparison theory.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib stores cone coordinates in the opposite order from the displayed
paper convention; the existing public projection formulas already account for
that order. The proof verifies those exact formulas, including the negative
fourth coordinate and negative cone boundary.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
