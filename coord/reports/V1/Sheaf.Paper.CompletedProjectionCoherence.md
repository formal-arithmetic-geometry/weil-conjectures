## What changed

Proved the completed tensor insertion maps, completed pullback unit, completed adjunction mate unit equation, uniqueness, limit equation, transpose compatibility, and simultaneous naturality in `Sheaf.Paper.CompletedProjectionCoherence`. Added a separate public data module and split three genuinely independent quotient-tower results into documented modules.

Reviewer correction (NT-cc): the tensor-model descent helper `flat_localization` now uses the proved, recorded `SheafOfModules.site_derived_tensor_descent_independentCoefficients` (node `lem-weil-pbc-site-derived-tensor-descent`) instead of the unrecorded `sorry` theorem `SheafOfModules.wf_site_derived_tensor_descent`; flatness is matched through `siteSheafTensorRightIso`.

## Proved and sorry left

Closed the original theorem's completion, adjunction, transpose, uniqueness, limit and naturality proof components. The retained split declarations are `CategoryTheory.AdicSites.quotientAugmentation_pullback`, `CategoryTheory.AdicSites.perfectQuotientProjection`, and `CategoryTheory.AdicSites.ProjectionCoherence.finiteQuotientTensorProjection`; each has exactly one documented `sorry`. The main theorem is proved from these three declarations and the completed-tensor construction.

The interface move is recorded in `coord/changes/completed-projection-route.md`.

## No longer needed

The item module no longer imports the proof-plan modules of the strict-diagram construction, which the split modules now carry or which the new route does not use: `Sheaf.Paper.CompletedPullbackAdjunction`, `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `Mathlib.CategoryTheory.Abelian.FunctorCategory`, `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`, `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`, `Sheaf.CategoryTheory.KInjectiveTotalDerived`, `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`, `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`, `Sheaf.Paper.ProEtaleProjectionFormulaArrows`, `Sheaf.Paper.ProjectionFormulaTotalization`, `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`, `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`. The private localization descent helpers remain needed for the arbitrary input tensor presentation. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

The eleven-step DAG proof treats strict quotient augmentation compatibility, perfect-coefficient projection invertibility, and finite quotient tensor evaluation coherence as if they were immediate consequences of the named declarations. Their conclusions are independent results with their own constructions, so they are split into separate documented nodes rather than hidden `sorry`s inside the main proof. The target statement and all existing public declarations are unchanged.

The item's statement uses declarations now recorded by `def-pur-completed-projection-data`; that node belongs in the item's `stmt_deps`, which stage-3 tooling does not let the worker change.

## New nodes

- `lem-pur-quotient-tower-augmentation-pullback`
- `lem-pur-perfect-quotient-projection`
- `lem-pur-finite-quotient-tensor-projection`
- `def-pur-completed-projection-data`

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
