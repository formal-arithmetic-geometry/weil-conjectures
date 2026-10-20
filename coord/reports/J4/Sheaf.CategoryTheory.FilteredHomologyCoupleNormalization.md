## What changed

Restored `Sheaf.CategoryTheory.FilteredHomologyCoupleNormalization` from its
quarantine archive and completely proved
`CategoryTheory.filteredHomologyCouple_normalization` without changing its
signature. Choose identity isomorphisms for D. The alpha equation is its explicit
definition after identity composition; the projection equation unfolds initialG,
the concrete couple, filteredHomologyG and filteredHomologyEIso, then cancels
all equality transports by simp. This works for every filtration, including zero
and constant ones; no boundedness or nonzero hypothesis is introduced.

Made `WeilConjectures.CategoryTheory.ExactCoupleConvergence` a public import,
as required by the public statement's use of initialG. Change record:
`coord/changes/filtered-homology-normalization-public-import.md`.
The existing two-step DAG proof already describes this exact argument and its
three definition dependencies; no route or node changes are necessary.

Validation: the restored module compiles cleanly through lcompile.py. A separate
scratch consumer importing only this module also compiles, using initialG and
extracting the quotient equation from the theorem. Its `#print axioms` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. The archived sole
consumer's application was checked against the preserved signature. The scratch
check is outside the delivered Lean tree.

## Proved and sorry left

Closed the single archived hole in
`CategoryTheory.filteredHomologyCouple_normalization`
(node `lem-sp-filtered-homology-couple-normalization`): 1 of 1.
No holes remain in the delivered module. No holes added or split off.

## No longer needed

Removed the redundant direct proof import
`Sheaf.CategoryTheory.FilteredHomologyCoupleData`, which remains publicly
available through `Sheaf.CategoryTheory.FilteredHomologyExactCouple` and is still
used by the proof. No mathematical dependency, node or module is pruned.
The convergence module remains needed for initialG. No new intermediate theory
is needed: the existing explicit definitions suffice.

## Where the brief, the DAG or earlier work was wrong

The archived module privately imported ExactCoupleConvergence despite using
initialG in its public theorem statement. The compiler explicitly requires the
public import. This is the recorded quarantine failure, now repaired. The
mathematical statement and the DAG's identity-and-transport proof are correct;
the unit route is preserved. No source-library changes or forced adaptations.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
