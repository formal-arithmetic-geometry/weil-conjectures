## What changed

Repaired the duplicate-proof return by deleting all four duplicate private helpers from
`Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen`: `dimensionAt_openEmbedding`,
`fibre_dimension_target_open_immersion`, `fibre_dimension_resLE`, and
`local_exists_bounded_fibre_dimension_neighbourhood`. The openness proof now imports
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound` and applies its existing
`AlgebraicGeometry.exists_bounded_fibre_dimension_neighbourhood` theorem.

In that unclaimed module, made only the existing neighbourhood theorem public, added
its source/proof docstring, and added the public local-dimension import required by its
statement. Its hypotheses, conclusion and proof are unchanged. The other three helpers
remain private in their original module. No consumer requires a source adaptation.
Updated the openness node to describe the reuse and attached the existing helper to a
new DAG node. The affine-local Stacks route and the unit's realized statements stay.

Change record: `coord/changes/Q7-local-fibre-dimension-reuse.md`.

Validation: both delivered modules compile through `lcompile.py --all`. Of the four
unchanged direct importers, `EllAdicProperTruncationBound`,
`ProperDerivedDirectImageCoproducts`, and `LowerShriekFunctoriality` also compile against
the sandbox. The attempted `UpperShriek` check stops at an unavailable published object
for its unrelated import `Sheaf.CategoryTheory.RightDerivedFunctorUpperBound`, before
elaborating the consumer. No adaptation is justified: the only interface changes add
visibility, and the helper previously had no external users. Consumer copies used for
these checks were unchanged and are excluded from the delivery.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.isOpen_localFibreDimension_le`
(`lem-weil-pbc-local-fibre-dimension-open`). Both delivered Lean modules contain zero
`sorry`. Added zero holes and split off zero obligations. The promoted theorem
`AlgebraicGeometry.exists_bounded_fibre_dimension_neighbourhood` retains its existing
complete proof. This is reuse of an existing proof, not a decomposition into new holes.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension` and
`Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`. Their theorems are used
by the existing neighbourhood proof, so neither module is globally pruned.

The item's direct proof dependencies `def-weil-finite-type-morphism`,
`def-weil-affine-spectrum`, `def-pc-scheme-fibre`,
`lem-weil-pbc-dimension-at-point-open-subspace`,
`lem-sbc-affine-coordinate-fibre-dimension`, and
`lem-weil-pbc-fibre-dimension-bounded-open-upstairs` are now encapsulated by the helper
node. They remain dependencies of that node; none is claimed globally unnecessary.
Removed the three old direct `tool_uses` approvals for the open-subspace, coordinate
comparison, and bounded-open-upstairs nodes from the openness node because it now
uses them through the helper. No library module is withdrawn.

All four copied helper bodies listed above are unnecessary and removed from the item.
No replacements or renamed duplicate proofs are introduced.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily reproduced four existing private theorems from
`FiniteTypeFibreDimensionBound`. The earlier report's claim that nothing was wrong
missed that duplication. The return is repaired by reusing the existing theorem in place.
Its private visibility required the documented additive interface repair; simply importing
its module would not have made the theorem callable. No mathematical statement changes.

## New nodes

`lem-weil-pbc-bounded-local-fibre-dimension-neighbourhood` records the already proved
neighbourhood helper in `FiniteTypeFibreDimensionBound`, now made public in place.
This adds a DAG attachment, not a new Lean statement, module or proof obligation.
The node has the original affine-local proof, source and dependency declarations.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
