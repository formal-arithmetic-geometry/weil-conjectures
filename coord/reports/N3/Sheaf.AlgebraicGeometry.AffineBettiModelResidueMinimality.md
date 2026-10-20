## What changed

Restored `Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality` from the
quarantine source recorded in `coord/rework.tsv`. Its theorem
`AlgebraicGeometry.Scheme.affine_betti_model_residue_minimality` already has a
complete proof: finite free residue terms have the prescribed Betti dimensions,
finite-dimensional cycles and homology force the residue differential to vanish,
and scalar-extension coordinates then force the differential over the residue
field of the affine evaluation kernel to vanish.

The delivery also adapts the restored
`Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology` interface with an
explicit public import of `WeilConjectures.AlgebraicGeometry.DerivedCategory`.
This makes its existing public signature self-contained after the retired
duplicate Sheaf `DerivedFiberBetti` module and ensures the assigned module
recompiles against the adopted source tree. The theorem signature and proof are
unchanged. The interface change is recorded in
`coord/changes/N3-affine-free-derived-category-import.md`.

## Proved and sorry left

The restored assigned theorem
`AlgebraicGeometry.Scheme.affine_betti_model_residue_minimality` is complete and
contains no `sorry`. The archived source also contained no holes. No new
statement or definition is added, and no `sorry` remains in either delivered
module.

## No longer needed

No proof dependency is pruned. The assigned proof uses
`Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology`,
`def-sc-derived-fiber-betti`, and `def-weil-residue-field`, together with the
Mathlib finite-dimensional and tensor-product APIs. The direct source import of
`WeilConjectures.AlgebraicGeometry.DerivedFiberBetti` is retained in the assigned
module because its theorem signature needs that public API.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine restoration, not an unfinished theorem: its rework row
preserves a complete source with zero holes. The published compile artifact still
contained the retired `Sheaf.AlgebraicGeometry.DerivedFiberBetti` declaration;
when the restored theorem imported the adopted upstream declaration directly,
that stale artifact caused a duplicate declaration. Recompiling the restored
comparison module and explicitly exposing `DerivedCategory` resolves the stale
interface without changing any mathematical statement. The DAG proof plan and
its existing node remain valid.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
