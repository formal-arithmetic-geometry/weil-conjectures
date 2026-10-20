## What changed

Retired the unused duplicate module
`Sheaf.AlgebraicGeometry.FiniteRelationDescent`, as assigned by the queue's
`retire` entry. `deleted.txt` requests withdrawal; the delivery tool leaves an
empty module. Reattached `lem-pc-fp-relation-descent` to the existing proved
`AlgebraicGeometry.finiteRelation_module_map_descent` in
`WeilConjectures.AlgebraicGeometry.FiniteRelationDescent`.

The retained source theorem has the same conclusion and hypotheses except that
it drops the unnecessary Noetherian-stage-ring assumption. A remote compile
verified that a single application of the source theorem proves the complete
old Sheaf signature. `#print axioms` for the retained theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`. The original Sheaf module also
compiled before withdrawal. No adopted source declaration or file was changed.

Change record: `coord/changes/B6-finite-relation-descent-retirement.md`.

## Proved and sorry left

Actual original holes: 0. Holes closed: none. Holes added: none. Holes left in the
withdrawn module: none. No split-off statements or new nodes.

The retained source theorem is already proved with only the three permitted
axioms. This delivery is duplicate retirement, not a claim to have newly proved
its theorem. The former signature is preserved as a consequence of that theorem.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FiniteRelationDescent`, including its two
private proved helpers and duplicate public theorem. No Lean module imports it:
`tools/downstream.py` reports zero downstream modules, and an import search in
both roots agrees. The sole external theorem application is already in
`WeilConjectures.AlgebraicGeometry.FinitelyPresentedComplexDescent`, importing
the source module. No consumer changes are required.

The retired copy's imports disappear with it:
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.RingTheory.Noetherian.Basic`,
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`,
`Mathlib.CategoryTheory.Adjunction.Additive`, `Mathlib.Data.Finset.Order`, and
`WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapDescent`.
They remain available to the retained source proof and are not claimed globally
pruned. The existing node and all its proof dependencies stay; only its Lean
attachment changes. `sk-thm-picard-semicon` has empty realized statement/step
arrays, and no unit statement or proof step is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with holes or an assigned repair.
This item instead has zero holes and is explicitly marked `retire` in the queue.
Its DAG attachment still points to the redundant Sheaf copy even though the
source library already contains the proved theorem and its consumer already
uses that source module. The node attachment is corrected in this delivery.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
