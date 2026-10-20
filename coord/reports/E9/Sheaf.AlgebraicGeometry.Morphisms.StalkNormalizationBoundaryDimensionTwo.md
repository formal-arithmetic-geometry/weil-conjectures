## What changed

Completed the retirement listed in `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`.
The duplicate is withdrawn through `deleted.txt`.
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths`
now imports the upstream twin and applies its theorem without the unused `hs`
argument. Its signature is unchanged. A theorem-local unused-variable linter
setting retains that public binder without a warning.

The node `lem-sbc-stalk-normalization-boundary-dimension-two` now records the
upstream theorem and its exact signature. Its statement, proof route and
mathematical dependencies are preserved, including the parent formal-depth node
and the unit `sk-prop-input-spreading`.

Change record:
`coord/changes/E9-retire-stalk-normalization-boundary-dimension-two.md`.

Validation: the adapted consumer compiles through `lcompile.py`; the delivery
runs the axiom probe and preflight. Mathlib searches were recorded through
msearch.py (LeanFinder, Loogle and grep), and direct source search found the
already proved upstream twin. No upstream file is edited.

## Proved and sorry left

This is a duplicate-retirement repair with zero original holes.
`AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two` was already
proved in the Sheaf module and is retained through its existing upstream theorem.
The consumer `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_formal_boundary_depths`
remains proved. Holes closed: 0. Holes added: 0. Holes left in the delivered
consumer and withdrawn item: 0. No theorem is split off.

## No longer needed

Retired module:
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`.
Its sole consumer removes that import and replaces it with
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`.

Withdrawal also removes the duplicate's proof imports of
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`
and `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoTransfer`,
and its public imports of Mathlib's Noetherian, QuasiSeparated, Smooth,
Normalization and KrullDimension.Basic modules, the source FiniteEtale module,
and the source Depth module. The consumer already has the statement imports it
needs. The upstream proof retains its own target-dimension and going-down
arguments. The Sheaf transfer module now has no Lean importer; its node is not
deleted or falsely claimed mathematically unnecessary. No mathematical node or
unit step is pruned: the boundary-dimension node is reattached to the upstream
proof and the formal-depth parent continues using it.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof obligation. This assignment is
instead explicitly listed as a retirement: the current module has zero sorry,
and the upstream theorem already proves the same conclusion with only the unused
hs hypothesis omitted. Repeating the dimension argument or creating another
intermediate theorem would duplicate existing work. The former DAG Lean record
still pointed to the Sheaf copy; this delivery corrects that attachment.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
