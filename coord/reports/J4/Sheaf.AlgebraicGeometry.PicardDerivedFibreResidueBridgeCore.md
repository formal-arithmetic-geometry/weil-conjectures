## What changed

Filled `AlgebraicGeometry.Scheme.picard_derived_fibre_residue_bridge_core` by applying
`picard_residue_homology_chosen_geometric_data`, then applying the fixed-model geometric
compatibility theorem and packaging the represented arrow as `DerivedCategory.Q.map (φ i)`.
Added the proof-only import of `PicardDerivedFibreResidueGeometricCompatibility` and the
public imports needed by the unchanged theorem statement. Added the new split module and
its DAG node.

## Proved and sorry left

Closed the original sorry in `AlgebraicGeometry.Scheme.picard_derived_fibre_residue_bridge_core`.
The delivery adds one strictly smaller named theorem with a sorry:
`AlgebraicGeometry.Scheme.picard_derived_fibre_residue_geometric_compatibility`, recorded in
`new-picard-derived-fibre-residue-geometric-compatibility`.

## No longer needed

Removed the proof-only/public imports of `Sheaf.AlgebraicGeometry.AffineResidueModelNaturality`,
`WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative`,
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`, and `Mathlib.AlgebraicGeometry.Fiber` from
the core module. The direct proof uses the already compiled affine family theorem instead.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted a declaration for the geometric residue-to-structure-sheaf
compatibility needed after the affine family theorem. Importing the existing geometric
comparison modules would create a cycle through the bridge, so that missing step is split
into a smaller theorem in its own module. The original core statement and all its binders
are unchanged.

## New nodes

`new-picard-derived-fibre-residue-affine-data` is a proved affine-data helper used by the core.

`new-picard-derived-fibre-residue-geometric-compatibility` is the named geometric
compatibility step. Its module contains the exact fixed-model hypotheses and conclusion,
with the source and proof plan recorded in its docstring and node file.

The import interface change is recorded in `coord/changes/PicardDerivedFibreResidueBridgeCore-imports.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueAffineData": "ba76075a148eb5815b52bb491e5140e92c4ea859", "Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore": "9330cae1e2e048fb1e24a8f605f9eccf927a8e1f", "Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueGeometricCompatibility": "f698a42d961878e60e78e10a8b49069507fe2861"}, "results": {"Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge": {"hash": "4c7d05990bb9f7dda068f72047f2065ab7ec4c0c", "status": "SLOW"}}, "seconds": 77, "time": "2026-10-28T13:13:36+0800", "transitive": 0, "version": 1}
```

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
