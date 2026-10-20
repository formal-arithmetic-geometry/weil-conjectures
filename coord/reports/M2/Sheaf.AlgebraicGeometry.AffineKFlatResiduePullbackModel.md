## What changed

Restored and repaired `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` in
its sandbox. The theorem proof is the existing canonical affine K-flat residue
pullback construction, with imports adapted to the adopted `WeilConjectures`
source modules after the upstream sync withdrew the old Sheaf copies. Added the
standard scalar-extension additive instance needed for the unchanged derived
complex statement and removed the empty `Sheaf.Algebra.Homology.KFlatPullback`
proof import. No theorem signature, target statement, or definition changed. The interface repair is recorded in `coord/changes/affine_kflat_residue_pullback_model_source_imports.md`.

## Proved and sorry left

Proved the sole declaration
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model` from
`lem-sc-affine-kflat-residue-pullback-model`. No `sorry` remains and no new
`sorry` was added.

## No longer needed

Removed the import `Sheaf.Algebra.Homology.KFlatPullback`, which is an empty
withdrawn module and contributes no declaration. The proof uses the adopted
source declarations `WeilConjectures.AlgebraicGeometry.DerivedPullback`,
`WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`, and
`WeilConjectures.Algebra.Homology.KFlat`.

## Where the brief, the DAG or earlier work was wrong

The quarantined prior delivery referenced Sheaf copies that were withdrawn by
the upstream sync. The current source tree exposes the same APIs under
`WeilConjectures`; using those modules is required for the item to compile.
The adopted source tree also lacks a global additive instance for
`ModuleCat.extendScalars`, so the module registers the standard instance from
`extendRestrictScalarsAdj`. This is an elaboration repair only; the public
statement remains byte-for-byte unchanged. No DAG statement or unit route was
changed.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
