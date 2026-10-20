## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StalkDerivedExtensionComparisonIsIso.lean`
from its current `coord/rework.tsv` quarantine path, preserving its declaration,
docstrings, proof, and DAG attachment. Added the explicit public import
`Sheaf.Algebra.Homology.KFlat`, because the public statement uses
`CochainComplex.IsAcyclicTensorKFlat`. The upstream source now exposes the distinct
name `CochainComplex.IsKFlatTensor`; importing the upstream stalk transport alone
does not expose the older predicate.

The archived original reproduces the recorded invalid-field error at line 65.
The restored file with the added import compiles cleanly through `lcompile.py`
in 7.3 seconds. No source-library file was changed.

Change record: `coord/changes/M2-stalk-derived-extension-kflat-import.md`.

## Proved and sorry left

This is a zero-hole restoration and import repair. The archived module had zero
`sorry`s; the delivered module has zero. Holes closed: none (0 of 0).
Holes added or split off: none (0).

`AlgebraicGeometry.SingleComplexBaseChange.stalkDerivedExtensionComparison_isIso`
retains its complete proof: the stalk criterion makes the scalar-extension
counit invertible on K-flat representatives; cancellation proves componentwise
invertibility there, and naturality along `Coordinates.e` transports it to every
derived object. The final step is `NatIso.isIso_of_isIso_app`.

## No longer needed

None. All three original imports and all four declared proof dependencies remain
needed. No module or DAG node is withdrawn, including quarantined parents. The
unit route and the item's existing Lean attachment remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned post-sync repair with zero holes, rather than an open
proof obligation. Its archived header omitted the public import of the predicate
appearing in its statement. The current upstream dependency's public interface
uses `IsKFlatTensor`, so it no longer supplies `IsAcyclicTensorKFlat` transitively.
The repair explicitly imports the existing Sheaf predicate and does not rename
or weaken the theorem's hypothesis. No new mathematical result is required.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
