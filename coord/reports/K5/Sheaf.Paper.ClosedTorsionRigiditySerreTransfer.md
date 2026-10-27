## What changed

Repaired the assigned rework import failure from `coord/rework.tsv` (2026-10-24,
reason: imports `Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero`). Removed unused
proof-only imports from `Sheaf.Paper.ClosedTorsionRigiditySerreTransfer`.
The two routes into the failing dependency were
`ScalarMatrixInverseImage -> FiniteConstantLocalModel -> ContinuousCoefficientCommRing`
and `InternalModuleOperationsTransport -> ContinuousCoefficientCommRing`; both then
entered the derived base-change / projective-line duality chain.

The canonical restriction definitions, all declaration signatures, public imports,
and the existing theorem hole are unchanged. This is an import-graph rework repair,
not a proof of the transfer theorem. Change record:
`coord/changes/K5-closed-torsion-rigidity-import-rework.md`.

## Proved and sorry left

Original holes: 1. Closed: 0. Added: 0. Split off: 0.
The single remaining hole is
`AlgebraicGeometry.ProEtale.CondensedRing.closed_torsion_rigidity_serre_transfer`
(node `lem-sfb-closed-torsion-rigidity-serre-transfer`). Both restriction definitions
retain their actual constructions with no data holes. No theorem was weakened or
relabelled. This delivery completes the listed rework repair without claiming proof
progress.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage`
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.AlgebraicGeometry.Sites.Proetale`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Adjunction.Limits`

These imports are unused by the current declarations and their proof bodies.
In particular the two imports introducing the failed projective-line dependency
are unnecessary for construction or elaboration of the actual restriction maps.
The retained private imports are the basic coefficient construction and exact
module inverse image.

No mathematical node is withdrawn. The future proof still needs a valid argument,
so its anticipated DAG proof dependencies have not been erased merely because
its current body is `sorry`. No module is deleted. No upstream declaration is
changed. The main node's Lean attachment and all parent references are preserved.

## Where the brief, the DAG or earlier work was wrong

The main node's Step 2 says the finite-complex-heart filtered closure theorem
holds on arbitrary qcqs schemes. Its dependency
`lem-sfb-qcqs-finite-complex-heart-filtered-closure` now records the corrected
`noetherian_finite_complex_heart_filtered_closure`, with
`[IsLocallyNoetherian X] [CompactSpace X]`. Its reviewed node and the NY/NV reports
explicitly refute the former arbitrary-qcqs version. The present theorem assumes
only qcqs, so that application is unavailable. This does not by itself refute
the present restriction theorem, and no unsupported Noetherian instance or new
replacement `sorry` has been introduced. A proof worker must repair that route
before claiming this theorem proved. The accepted theorem statement is preserved.

Searches actually run in this session: LeanFinder for closed torsion rigidity on
the weak Serre coproduct hull (eight condensed-module hits, no exact result),
Loogle for the weakSerreCoproductClosure name (service did not recognize this
project identifier), msearch grep for torsion/rigidity (zero Mathlib hits), and
local rg across both library roots. Read the weak Serre universal property,
supported three-term scalar rigidity, finite-heart presentation definitions,
the corrected Noetherian closure theorem, and its review explaining the gap.

`tools/downstream.py ... --uses closed_torsion_rigidity_serre_transfer` reports
zero downstream modules and only the declaration in the item itself. This is
not used to justify withdrawal: the DAG parent still requires the item.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
