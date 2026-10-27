## What changed

Filled `RingTheory.Sequence.polynomial_regular_sequence_syzygies` without changing its signature.
Polynomial regularity comes from Mathlib's `IsRegular.of_faithfullyFlat`, using the monomial
basis of the multivariate polynomial ring. Three proved private helpers calculate the first
two Koszul differentials and convert Koszul regularity to the explicit triangular syzygy
formula. The conversion uses the existing regular-to-Koszul theorem, degree-one exactness,
and the exterior-square basis; no new public statements or modules are introduced.

Updated the item's node proof, proof dependencies, and proof origin to record this route.
The exterior-power basis dependency is an existing Mathlib leaf. The unit statement and route
are unchanged. All work is confined to the item and its node.

Searches: LeanFinder for first syzygies of regular sequences, Loogle for
`RingTheory.Sequence.IsRegular`, and msearch grep for `IsRegular.of_faithfullyFlat|syzyg`.
Also searched the project RingTheory and Koszul modules and read Mathlib Regular/Flat,
ExteriorPower/Basic, ExteriorPower/Basis, and Finsupp/LinearCombination. No existing theorem
supplies the full syzygy formula. The faithfully flat theorem supplies the first clause.

## Proved and sorry left

Closed 1 original hole: `RingTheory.Sequence.polynomial_regular_sequence_syzygies`
(node `lem-trf-polynomial-regular-sequence-syzygies`).

The private helpers `boundary_zero_formula`, `boundary_one_formula`, and
`syzygies_of_isKoszulRegular` are all proved. No holes added, no split-off statements,
and no `sorry` remains in this module. This is a proof, not a decomposition.

Validation: remote single-file compilation passed cleanly in 7.5 seconds, with no
warnings or errors. The delivery command performs the final compile and preflight checks.

## No longer needed

The coefficientwise ideal-membership calculation formerly planned in steps 1 and 2 is
replaced by Mathlib's faithfully flat base-change theorem. There was no separate node or
module for that elementary calculation, so no existing mathematical dependency is pruned.

Removed redundant private imports `WeilConjectures.RingTheory.KoszulRegularSequence`,
`WeilConjectures.AlgebraicGeometry.KoszulComplex`, and
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`; these are already publicly
provided by the regular-to-Koszul dependency. Their declarations remain used.
The three original public imports are preserved.

All original proof-dependency nodes remain needed. The exterior-power basis node
`lem-weil-pbc-exterior-power-free-basis` and free-module definition are now cited explicitly
in the proof dependency list. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The polynomial regularity clause has
a shorter existing Mathlib proof than the coefficient argument in the original plan.
The syzygy coordinate argument works also for the empty sequence, so `hs` is unnecessary
for that argument; its binder is preserved exactly as required. The two-element-subset basis
has no indices when the sequence has length one, giving the required zero-vector conclusion.
For zero variables the polynomial argument still applies; no positivity of `m` is used.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
