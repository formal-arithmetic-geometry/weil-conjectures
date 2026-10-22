## What changed

Restored lean/Sheaf/AlgebraicGeometry/RelativelyFlatDerivedBaseChangeComplex.lean,
which is absent under its current quarantine rework assignment, as a compatibility
re-export of the adopted source theorem. The archive is preserved. The shim also
publicly imports Sheaf.Algebra.Homology.KFlat so that the archived K-flat hypothesis
remains expressible. No new declaration, instance or definition is introduced.

Repointed lem-pc-rf-base-change-complex's lean record to the adopted source theorem
and recorded its exact signature. Corrected the description of proof step 2 to the
current source criterion API; all mathematical proof dependencies are retained.

The restored shim compiled in 3.9 seconds. A separate consumer reproducing the full
archived theorem signature compiled in 12.8 seconds by applying the source theorem
with every original argument. Both its axiom check and the source theorem's show
only propext, Classical.choice and Quot.sound. The only signature spelling change is
IsAcyclicTensorKFlat to IsKFlatTensor; their definitions are identical. Import-direction
checking permits the restored shim to import the source module.

Change record: coord/changes/A4-relatively-flat-derived-base-change-source-compatibility.md.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived module had 0 sorry holes;
0 holes closed and 0 holes added; none split off. The restored module has 0 holes.
AlgebraicGeometry.relativelyFlat_derivedBaseChange_complex is supplied by its existing,
fully proved adopted source declaration (lem-pc-rf-base-change-complex). No new proof
of that result is claimed. There is no remaining sorry in this delivery.

## No longer needed

The duplicate archived declaration and its private tensor_cancel_iso and
baseChange_naturality implementations are not restored: the source theorem already
provides the full proof. The shim needs none of the archive's four private imports
as direct imports: DerivedPullbackTorIndependentFlatComplex,
SingleComplexBaseChangeCriterion, CounitStalkConditionFromLocalizedComparison and
TensorCounitOneKFlatCoordinates are still used by the adopted source proof. Their
nodes and modules are not pruned. The archive's statement imports are provided by
the source module, with the legacy K-flat vocabulary explicitly retained.

No mathematical dependency, parent node or module is withdrawn or pruned. In particular,
zero live importers of the missing module does not make the result unnecessary:
the archived RelativelyFlatTensorBaseChangeIso consumer and its DAG parent still use it.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole repair, rather than a live module with sorry.
The unchanged archive fails because IsAcyclicTensorKFlat and
SingleComplexBaseChange.counit are only privately imported; the restored shim
publicly exposes both through its two imports.
The adopted source theorem is already present and proves the archived proposition.
The old attachment still named the absent Sheaf declaration. Its step 2 described a
boundedness argument no longer required by the source single-complex criterion;
the source theorem still uses the stated upper bound in its stalkwise comparison.
The restored path and corrected attachment retain the mathematical statement and
unit route. No target statement, definition or source-library declaration is changed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
