# AlgebraicGeometry.Etale.ordinaryFiniteLine

## Reason

Name the existing degree-zero single-functor object construction once and use it
in both the ordinary finite line and signed-twist object. This lets the kernel compare
the sheaf arguments before unfolding the large concrete single functor. The wrapper
constructs exactly the original object, with no selected data or proof obligation.
The Chern specification passes its original arrow; a local transparency option lets
elaboration unfold the definitionally identical degree-zero wrapper.
All existing declaration signatures are unchanged. The newly landed P2 Kummer
performance repair is preserved. A direct public import of the coefficient interface
records what those signatures need: the current source already reexports it through
the scalar-comparison umbrella, but the older published umbrella does not.

Reviewer correction (2026-10-24): because `ordinaryFiniteDegreeZero` is a plain `def`,
instance search no longer sees Mathlib's `IsGE`/`IsLE` instances for
`(singleFunctor _ 0).obj F` through `ordinaryFiniteLine`. Three consumers failed with
`failed to synthesize DerivedCategory.TStructure.t.IsGE (Etale.ordinaryFiniteLine …) 0`
(`SpP1NormalizedFamilyCore`, `BaseChangedLineTraceEvaluation`, `ProEtaleProjectiveLineTrace`).
Two public instances on the wrapper, `ordinaryFiniteDegreeZero_isGE` and
`ordinaryFiniteDegreeZero_isLE`, restore exactly the instances the old abbreviation
exposed; the item's private copy of the `IsGE` instance is removed.

## Old

```lean
abbrev ordinaryFiniteLine (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine T N A hA)
```

```lean
def ordinaryFiniteP1ChernSpec (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) : Prop :=
  ordinaryFiniteClass A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2 c =
    ordinaryFiniteP1KummerClass A N hA S hP
```

## New

```lean
def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj F
```

```lean
instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsGE
    ((DerivedCategory.singleFunctor _ 0).obj F) 0)

instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.singleFunctor _ 0).obj F) 0)
```

```lean
abbrev ordinaryFiniteLine (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  ordinaryFiniteDegreeZero A T (Scheme.finiteEtaleTateLine T N A hA)
```

```lean
set_option backward.isDefEq.respectTransparency false in
def ordinaryFiniteP1ChernSpec (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) : Prop :=
  ordinaryFiniteClass A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2 c =
    ordinaryFiniteP1KummerClass A N hA S hP
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineLinearActionFamily` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.OriginComparisonArrows` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineDiagonalTateCoordinates` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.CoordinateCounitArrows` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.FiniteSiteCoordinates` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.IntegrationExponentTransposeTransport` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.OrderedAffineTraceNormalForm` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.P1KummerDerivedScalar` | U1 | definitionally identical object; no adaptation |
| `Sheaf.Paper.P1KummerScalarEndpoints` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.ProEtaleProjectiveCoefficient` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.Paper.VectorTraceScalarDescent` | unclaimed | definitionally identical object; no adaptation |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | U8 | definitionally identical object; no adaptation |

| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | definitionally identical interface; no adaptation |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | definitionally identical interface; no adaptation |

## Status

landed 20261024T191435-L-356888 2026-10-24 (merge of deliver/U8/Sheaf.AlgebraicGeometry.GeoP1Cohomology)
