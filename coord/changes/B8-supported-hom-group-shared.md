# AlgebraicGeometry.SupportHomPair.group

## Reason

Use the existing `Sheaf.supportHypercohomologyFunctor` definition for the degree-a
supported cohomology group. The previous body expands precisely that functor's
composition. Naming the already-defined functor aligns the type of the normalized
comparison with the type of the actual supported group and avoids repeatedly
expanding its derived-category construction during kernel checking.

The old/new equation is reflexivity: the named functor is defined by the same
composition of right-derived supported sections and degree-a homology. No binder,
universe, mathematical statement or normalization changes. All original public
imports remain verbatim; the support-cohomology interface is already publicly
imported. All identification, coefficient-change, exchange and coherence proofs
remain in the assigned file; none is split to avoid the file limit.

Targets using this definition need renewed statement review. Definitional equality
preserves their meaning. No adopted source-library declaration is edited.

## Old

```lean
abbrev group (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :=
  (S.sections.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).obj K
```

## New

```lean
abbrev group (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :=
  (Sheaf.supportHypercohomologyFunctor S.topology
    (ModuleCat.{u + 1} A) S.restriction a).obj K
```

## Users

The listed downstream statements keep the same cohomology objects. No existing
downstream proof explicitly unfolds SupportHomPair.group. The old and new
formulas are definitionally equal, and no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Reuses the existing support-cohomology functor, with the same object formula. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |

## Status

landed 20261022T025316-L-1272250 2026-10-22 (merge of deliver/B8/Sheaf.Paper.SupportedHomPullback)
