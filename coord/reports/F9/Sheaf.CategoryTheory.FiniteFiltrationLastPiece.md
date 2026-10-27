## What changed

Filled `CategoryTheory.DecreasingFiltration.finite_filtration_last_piece` in
`Sheaf.CategoryTheory.FiniteFiltrationLastPiece`, preserving its statement and imports.
The proof follows the four existing DAG steps: zero graded pieces make successive
inclusions epi and hence invertible; bounded integer induction identifies the steps
with the full subobject; the final quotient is invertible because its defining map
has zero source; composition of the canonical isomorphisms gives the unique lift,
the specified comparison inverse, and transport of the zero-object property.
Mathlib supplies the mono-plus-epi and cokernel universal-property arguments.

## Proved and sorry left

Closed the one original hole in
`CategoryTheory.DecreasingFiltration.finite_filtration_last_piece`
(node `lem-weil-pbc-finite-filtration-last-piece`). Added zero holes; zero remain.
No split-off declarations, new definitions, or statement changes.

## No longer needed

None. All existing imports and declared proof dependencies remain used. No node or
module is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. Search found the upstream
`DecreasingFiltration.F_eq_top_of_isZero_gr`, but it assumes vanishing in every
integer degree below the cutoff, including negative degrees. The present bounded
vanishing hypothesis instead needs the bounded induction implemented here.
LeanFinder found ring/module filtration results, and Loogle returned
`kernelSubobject_comp_mono_isIso`; neither states this result. Grep identified the
Mathlib canonical subobject and cokernel isomorphism lemmas used in the proof.
The cases `n = 0` and zero `V` are included by the same proof.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
