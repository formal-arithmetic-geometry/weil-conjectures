## What changed

Repaired the two-module upstream-sync rework cluster. Restored
`Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels` and its quarantined consumer
`Sheaf.AlgebraicGeometry.AffineCoordinateTensorComparison` as public re-exports of
`WeilConjectures.AlgebraicGeometry.AffineCoordinateModuleModels` and
`WeilConjectures.AlgebraicGeometry.AffineCoordinateTensorComparison`, respectively.
The adopted source already implements every declaration and proves the whole
coordinate K-flatness and tensor/homotopy composition chain. Reusing it removes
the unavailable legacy-predicate reference and avoids duplicate declarations.

Updated the `lean` realization records of
`lem-pc-affine-coordinate-module-models` and
`lem-pc-affine-coordinate-tensor-comparison` to these source modules. The former's
record now uses the canonical predicate `IsKFlatTensor`; its definition is exactly
the former acyclic-tensor condition. The two mathematical node statements and
proof routes stay the same, including the unit's route.

Change record: `coord/changes/G8-affine-coordinate-source-reexports.md`.
It includes the old and new code, the API comparison, and the downstream-user audit.
No upstream file is edited.

Both restored modules compile independently (1.7 s and 1.6 s) through `lcompile.py`.
A consumer probe imports both restored paths and checks the re-exported API and
axioms. Import-direction checks accept both source imports.

## Proved and sorry left

This is a zero-hole rework repair: the quarantined item and its consumer each
already had zero literal `sorry`. Holes closed: 0 of 0. Holes added: 0.
Split off: 0. Holes left in the delivered modules: 0. This is not a new proof or
a decomposition; the existing complete source proofs are reused.

The seven coordinate declarations available from the repaired import are
`AlgebraicGeometry.affineCoordinateModules`,
`AlgebraicGeometry.affineCoordinateComplex`,
`AlgebraicGeometry.affineCoordinateModules_preservesZero`,
`AlgebraicGeometry.affineCoordinateComplexFactorIso`,
`AlgebraicGeometry.affineCoordinateModelIso`,
`AlgebraicGeometry.affineCoordinateModuleEquivalence`, and
`AlgebraicGeometry.affineCoordinateComplex_isKFlat`
(node `lem-pc-affine-coordinate-module-models`).

The consumer re-exports the fourteen declarations implementing global sections,
the affine adjunction and mates, the termwise and homotopy comparisons, and their
composition laws (node `lem-pc-affine-coordinate-tensor-comparison`). In particular
`AlgebraicGeometry.affineCoordinateTensorComparison_comp` and
`AlgebraicGeometry.affineCoordinateHomotopyComparison_comp` are fully proved.
`#print axioms` for all seven coordinate declarations and both composition laws
reports only `propext`, `Classical.choice`, and `Quot.sound`. Thus the source proof
chain has no reachable proof holes.

## No longer needed

The two restored Sheaf paths contain no copied declarations or copied proofs.
They remain compatibility re-exports; no module is claimed as globally pruned.

The item removes its former direct imports of
`WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonData`,
`Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`,
`Sheaf.Algebra.Homology.KFlatPullback`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`, and
`WeilConjectures.Mathlib.Algebra.Homology.Bifunctor`.
Only the source `AffineCoordinateModuleModels` module is now imported directly.
The source theorem still uses affine tilde K-flatness and pullback K-flatness:
nodes `lem-pc-affine-tilde-kflat` and `lem-pc-kflat-pullback-preservation` are retained,
not falsely reported as bypassed.

The consumer removes its former direct imports of
`Sheaf.AlgebraicGeometry.AffineCoordinateModuleModels`,
`Sheaf.AlgebraicGeometry.PerfectHomCochainCounit`,
`WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`,
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`, and
`WeilConjectures.CategoryTheory.AdjunctionSquareComposition`.
Only the source `AffineCoordinateTensorComparison` module is now imported directly.
Its source proof retains the adjunction-mate route and its dependency nodes;
there is no mathematical DAG pruning and no removed `tool_uses` approval.
These import removals concern the compatibility files, not the source library.

## Where the brief, the DAG or earlier work was wrong

The item is a rework repair rather than an unproved theorem. Both Sheaf files are
under `quarantine/`, absent from `lean/`, following the 2026-10-20 sync. Its recorded
failure is the old public reference to `CochainComplex.IsAcyclicTensorKFlat`; the
adopted source theorem uses `CochainComplex.IsKFlatTensor` for the same condition.
The DAG still pointed to the quarantined copies despite their complete source
twins. Those realization records are corrected in this packet.

The tensor-comparison twin uses
`ModuleCat.baseDerivedTensor_extendScalars_additive` in place of the old
`ModuleCat.extendScalars_additive_sheaf`. This changes only a proof of the same
additivity proposition, not the comparison's data or statement.

The required `msearch.py` searches completed: Lean Finder returned scheme-flatness
lemmas rather than this theorem; Loogle returned `Adjunction.leftAdjointUniq` and
its coherence lemmas; indexed grep returned no affine-coordinate declarations.
Direct `rg` and full source-file comparison found both exact source implementations.
`tools/downstream.py` cannot index a quarantined Sheaf module, so its users were
also checked by direct import search across `lean/` and `quarantine/`; the only
Sheaf consumer is restored in this packet. Canonical source downstream users
already import the same source definitions and need no adaptation.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
