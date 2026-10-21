## What changed

Retired the duplicate module
`Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` using `deleted.txt`.
The adopted source module
`WeilConjectures.AlgebraicGeometry.ProperFlatSingleNoetherianDescent` already
contains the complete theorem `AlgebraicGeometry.properFlat_single_noetherian_descent`
with the exact node statement. Reattached
`lem-pc-proper-flat-single-noetherian-descent` to that source declaration and
kept its proof steps and dependency edges unchanged.

Changed the sole live consumer,
`Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel`, only at its import:
it now imports the source twin. Its statements and proof body are unchanged.
The quarantined historical `ProperFlatSingleOpenNoetherianComparison` importer
is archival and remains untouched. Change record: `coord/changes/M4-proper-flat-single-noetherian-descent-retirement.md`.

## Proved and sorry left

This is a duplicate retirement. The old Sheaf module had zero `sorry`s and no
new declarations are added. Holes closed: 0. Holes added: 0. Holes left: 0.
The retained source theorem is complete and is the canonical proof of the node.

## No longer needed

The duplicate Sheaf module and its private helper proofs are no longer needed.
The imports that disappear from that duplicate are
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.AlgebraicGeometry.AffineScheme`,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
`WeilConjectures.AlgebraicGeometry.TensorPullback`,
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`,
`WeilConjectures.AlgebraicGeometry.EventuallyProper`,
`WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage`,
`WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. The source
proof retains the mathematical dependencies it needs through its own imports.
The consumer's import of the duplicate is replaced by the source import. No
DAG dependency or unit route is pruned, and no unfinished parent is bypassed.

## Where the brief, the DAG or earlier work was wrong

The prior DAG attachment pointed at the duplicate Sheaf copy even though the
adopted source library already contained the same complete theorem. The shortest
valid route is to reuse that source declaration. No mathematical statement is
disputed or changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
