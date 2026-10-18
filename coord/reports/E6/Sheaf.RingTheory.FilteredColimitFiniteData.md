## What changed

Proved `CommRingCat.exists_finite_data_stage` in
`Sheaf.RingTheory.FilteredColimitFiniteData`, with its signature unchanged.
The proof chooses representatives using Mathlib's concrete filtered-colimit API,
moves them to a finite common upper bound, obtains eventual equality witnesses
for the polynomial equations, and moves all witnesses to one later common stage.
Polynomial evaluation commutes with every transition because integer ring maps
are unique. This also proves the persistence clause.

Added proof-only imports of `Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.Data.Finset.Order`. Updated the existing node's proof and dependencies
to describe this implementation. All public imports and signatures are unchanged.

The module compiled through `lcompile.py` in 3.2 seconds with no warnings or errors.
The empty-element and empty-equation cases are included: `Finset.exists_le`
works for the empty first set using nonemptiness, and the second set explicitly
contains the initial common stage even when there are no equations.

## Proved and sorry left

Closed 1 hole: `CommRingCat.exists_finite_data_stage`
(node `lemma-nagata-filtered-colimit-finite-data`).
Added 0 holes; split off 0 theorems. No sorry remains in the delivered Lean module.
The proof uses Mathlib declarations and no unfinished project theorem.

## No longer needed

Removed the proof-only import `Sheaf.Order.DirectedFiniteUpperBound`.
This proof does not need `lemma-nagata-directed-finite-upper-bound`,
`def-nagata-directed-finite-upper-bound`, or the selected-upper-bound construction
and its recursion lemmas. Mathlib `Finset.exists_le` gives the existential finite
upper bounds needed here directly; no particular selected bound is in the
conclusion. The module and these nodes may remain needed by other parents.
Kept `lem-pc-filtered-colimit-commrings-elementwise`: its two Mathlib clauses
supply precisely the representative and equality witnesses used in the proof.
No other planned dependency is unused, and no other import was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original proof plan's
selected finite-upper-bound dependency was stronger than this existential
statement needs. The argument follows the current blueprint's finite-stage
bookkeeping and preserves the approximation unit's route.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
