# ordinaryFiniteUnit, ordinaryFiniteUnitPullback, ordinaryFiniteDegreeZero_isGE, ordinaryFiniteDegreeZero_isLE

## Reason

The complete mate proof exceeded the file limit because the constant unit and
twist line used separately elaborated single-degree embeddings. Share the
existing `ordinaryFiniteDegreeZero` construction in `ordinaryFiniteUnit`, and
reuse the existing canonical `genericConstantIso` in `ordinaryFiniteUnitPullback`.

The generic constant comparison expands to the original single/constant
comparison, with exactly the original coefficient and scheme arguments.
The new constant-unit body expands, via `ordinaryFiniteDegreeZero` and
`ordinaryFiniteSingleFunctor`, to the original single-functor value. No data are
selected from an existence theorem, and no mathematical definition, hypothesis
or conclusion changes. The existing signatures, attributes, visibility and
docstrings stay unchanged. The arrows module adds
`public import Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators` because
its constant-comparison definition body uses `genericConstantIso`.

The degree-zero IsGE/IsLE instances use the existing functor equation explicitly
instead of conversion across the cached object. These are changes to proofs of
the same propositions. Both definition modules and the adapted identity module
are unclaimed. The affected target definitions are submitted for independent
meaning review under the definition-change rule; no Challenge statement changes.

## Old

```lean
def ordinaryFiniteUnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).obj (ordinaryFiniteUnit A Y) ≅
      ordinaryFiniteUnit A X :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))
```

```lean
abbrev ordinaryFiniteUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj (ordinaryFiniteConstant A T)
```

```lean
instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsGE
    ((DerivedCategory.singleFunctor _ 0).obj F) 0)
```

```lean
instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 :=
  inferInstanceAs (DerivedCategory.TStructure.t.IsLE
    ((DerivedCategory.singleFunctor _ 0).obj F) 0)
```

## New

```lean
def ordinaryFiniteUnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).obj (ordinaryFiniteUnit A Y) ≅
      ordinaryFiniteUnit A X :=
  genericConstantIso (ModuleCat.{u + 1} A) (ModuleCat.of A A) f
```

```lean
abbrev ordinaryFiniteUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T :=
  ordinaryFiniteDegreeZero A T (ordinaryFiniteConstant A T)
```

```lean
instance ordinaryFiniteDegreeZero_isGE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsGE (ordinaryFiniteDegreeZero A T F) 0 := by
  unfold ordinaryFiniteDegreeZero
  rw [ordinaryFiniteSingleFunctor_eq]
  infer_instance
```

```lean
instance ordinaryFiniteDegreeZero_isLE (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    DerivedCategory.TStructure.t.IsLE (ordinaryFiniteDegreeZero A T F) 0 := by
  unfold ordinaryFiniteDegreeZero
  rw [ordinaryFiniteSingleFunctor_eq]
  infer_instance
```

## Users

The table includes the union of whole-word declaration users from
`tools/downstream.py` for the two definition modules, with `--uses
ordinaryFinitePullback ordinaryFinitePushforward ordinaryFiniteUnitPullback
ordinaryFiniteUnit ordinaryFiniteDegreeZero_isGE ordinaryFiniteDegreeZero_isLE`.
The scans were repeated after the shared repository refreshed; earlier hits are
retained as a conservative superset. Each use denotes the same canonical object,
functor or morphism after expanding the aliases. The two concentration-instance
statements are unchanged, so their implicit consumers require no statement
adaptation. No consumer is weakened, strengthened or withdrawn.

The original `vectorIntegration_identity_unit` proof fails at
`rw [constant_identity]` because unfolding `ordinaryFiniteUnitPullback` now leaves
`genericConstantIso` around the constant-sheaf comparison. Its only tactic change
adds that name to the existing unfolding simp list. A private import of
`OrdinaryFiniteP1Arrows` records the direct proof dependency and ensures that the
changed arrows compile before this consumer in the sandbox. All existing
signatures and public imports of that consumer are preserved.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineLinearActionFamily` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineLinearActionRigidity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineLinearTraceAction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineLinearUniversalAction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceConstruction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionComparisonIsoPasting` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionOrientationMapExt` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionProjectionUnit` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionPurityUnitIsIso` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionPurityUnitNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.BundleSectionRankZeroAffineNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ChartSumAffineCounitTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate` | X5 | Assigned proof completed using the shared canonical comparisons. |
| `Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange` | X7 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.GabberRegularPairPurity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrderedTateSectionPullback` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows` | unclaimed | Reuse the canonical generic constant comparison; signature unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit` | Z8 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` | unclaimed | Share the cached unit embedding; explicitly rewrite two instance proofs. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OriginComparisonArrows` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.OriginProjectiveNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.RegularSupportedClassOperations` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | U3 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison` | U4 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransportData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.SupportedKummerLocalizationBoundary` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationDirectSumLocal` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationIdentityUnit` | unclaimed | Unfold genericConstantIso in the existing proof; private direct import. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility` | U2 | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationMate` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationSwapChartPrefix` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationSwapLocal` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent` | unclaimed | Forced private-proof adaptation: locally expose the two cached degree-zero wrappers for rewrite matching; statements unchanged. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineCoefficientCounitNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineCounitScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineDiagonalIntegrationConstructions` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineDiagonalPowerCoefficient` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineDiagonalRawTransposePower` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineDiagonalTraceRestriction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineDiagonalTransposePower` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineLinePurityCoordinateMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineOrderedIntegrationTransposes` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AffineTranslationTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CartierDualKummerNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ChartCounitScalarTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ChartGeometricCounitEvaluation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ChartTargetOpenDescent` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CoordinateCounitArrows` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CoordinateLineCounitTensor` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CoordinateSectionProjectiveTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalAffineTraceCoordinates` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalAffineTraceSiteData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalCounitComparisonData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalDncChartNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalExchangeNaturality` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationRigidity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrientationChartExistence` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrientationCharts` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrientationChoiceIndependent` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrientationCompatibility` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.DiagonalOrientationRefinementData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FieldOrientationSystemComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FieldOrientationSystemFiniteOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteOrientationReduction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteProductScalarPresentation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionLineChartScalars` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSiteCoordinates` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSiteTensorProjection` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.IntegrationExponentTransposeTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrderedAffineTraceNormalForm` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrderedIntegrationComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrderedTateScalarNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.OrientationEtaleFamily` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1CounitScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1KummerChernScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1KummerDerivedScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1KummerScalarEndpointComposition` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1KummerScalarEndpoints` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1KummerTraceSiteTransport` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.P1SplittingScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProEtaleOrderedIntegration` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProEtaleProjectiveLineTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProEtaleVectorIntegration` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProjectionUnitIntegration` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.PurityCompositionComparisons` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.PurityDiagonalDualizingData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.RamifiedCartierSupportedPurity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.RamifiedRootLimitTorsionUnit` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SectionCoordinateCounitNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerP1EtaleDelta` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.UniversalTranslationMultiplier` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorFrameIntegrationSiteDescent` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorIntegrationChartComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorIntegrationChartCoordinates` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorIntegrationUnitTranspose` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorModelChartDescent` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorPurityNormalization` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorTensorSiteEquations` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorTraceScalarDescent` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Paper.VectorZeroSectionIntegrationBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.DncCoefficientTransportData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRingData` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.ReductionExceptionalObjects` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.TransportAffineTrace` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SecSmoothPurity.TransportFiniteLineDerived` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SixFunctors.AffineDualizingCoefficient` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.SixFunctors.ProjectiveLineTraceModel` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | Same objects and arrows after alias expansion; statements unchanged. |

Validation: all five changed modules compile in the repaired set, including
`VectorTraceGeometricDescent`. The unchanged
`FiniteP1ChernAdjunctBaseChange`, `FiniteP1TwistedUnitBaseChange` and
`OrdinaryFiniteP1KummerMaps` also compile against the changed definitions.
The compile overlay rebuilt the unchanged scalar-faithfulness and fibre-homology
dependencies successfully. The original pullback and pushforward definitions,
including their generated instance lemmas used by the scalar-faithfulness
consumers, are preserved verbatim.


Repair of reviewer C-66dc5's return on `66dc52b8862` additionally adapts the
unclaimed `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent`. Its original
private `vectorIntegration_eq_of_normalization` fails against the changed
constant unit at 119:14 and 131:21: `rw [hell, ← Category.assoc]` cannot match a
composition because its instantiated pattern is not type-correct under implicit
transparency. The original compiles against the published build at 57.8 seconds.
The repair adds exactly one theorem-scoped attribute command before that private
proof: `attribute [local implicit_reducible] ordinaryFiniteDegreeZero
ordinaryFiniteSingleFunctor in`. It lets the existing rewrite tactics see the
same explicit single-functor objects through the cached wrappers. No existing
signature, visibility, public import, global attribute or proof step is changed.
The compiler error and changed line are also recorded in report.md under
`## Forced adaptations`.

## Status

landed 20261026T102419-L-357942 2026-10-26 (merge of deliver/X5/Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate)
