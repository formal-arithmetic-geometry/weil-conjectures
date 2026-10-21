## What changed

Restored `lean/Sheaf/AlgebraicGeometry/FlatDerivedStructureUnit.lean` from the
quarantine path recorded in `coord/rework.tsv`. The module's public
`Sheaf.AlgebraicGeometry.DerivedPullback` import was migrated to
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, because the former is now an
empty withdrawn stub. The theorem `AlgebraicGeometry.exists_flat_derived_structure_unit`
and its docstring and proof are unchanged. The module compiles together with the
already restored `FlatDerivedStructureUnitProperties` dependency.

## Proved and sorry left

The restored declaration `AlgebraicGeometry.exists_flat_derived_structure_unit` has
zero `sorry`s. No new declarations or `sorry`s are added. The proof constructs the
canonical single direct-image map, the two homology isomorphisms, their degree-zero
compatibility, and combines these with the existing fibre-properties theorem.

## No longer needed

No imports, nodes, or modules are pruned. All imports in the quarantined module are
retained; only the public source of `DerivedPullback` is migrated as required for the
restoration.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or DAG proof step was wrong. The rework quarantine left the
module absent from `lean/` while its former Sheaf compatibility import had become an
empty stub. Restoring the exact theorem therefore requires the source public import
migration recorded in `coord/changes/D3-flat-derived-structure-unit-restoration.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
