# AlgebraicGeometry.ProEtale.SpTowerClasses.FiniteChernNormalization

## Reason

Profiling found the existing normalization spending 52.4 seconds in kernel type checking, and its unchanged diagonal consumer also exceeded the per-file limit. Make the already inferred result types of forgetEvaluatedArrow and kummerComposite explicit, keeping both composite bodies verbatim. In FiniteChernNormalization bind the two compared arrows locally, and reuse evaluatedChern for the coefficient-linear evaluated arrow. This avoids rebuilding its evaluation and line-comparison expression in the normalization. A subsequent profiled item check passed in 49.2 seconds.

The normalization is definitionally equal to its old formula: unfold evaluatedChern and forgetEvaluatedArrow and reduce the two local lets. The explicit category Ab T is the same tower category previously inferred. The Kummer shift 1 + 1 is 2. All binders, actual maps, positive connecting convention, coefficient rings, and endpoint transports are preserved; no target statement or meaning changes. No irreducibility attributes are added.

## Old

```lean
def forgetEvaluatedArrow {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [HasDerivedCategory.{w₃} H]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {Z : D} (e : F.obj Y ≅ Z)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :=
  mapSingleArrow G (2 : ℤ)
    (mapSingleArrow F (2 : ℤ) a ≫
      ((DerivedCategory.singleFunctor D 0).map e.hom)⟦(2 : ℤ)⟧')
```

```lean
def kummerComposite {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] (s : ShortComplex C) (hs : s.ShortExact)
    {X : C} (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :=
  f ≫ hs.singleδ⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)
```

```lean
def FiniteChernNormalization {T : Scheme.{u}} (c : Chern l E T) : Prop :=
  ∀ (L : T.Pic) (n : ℕ),
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n))⟦(2 : ℤ)⟧')
      (forgetEvaluatedArrow (SpTowerShriek.ev l E T n) (finiteForget l E T n)
        (lineEvaluation l E c n) (firstChern l E c L))
      (mapSingleArrow (abEvaluation T n) (2 : ℤ)
        (kummerComposite
          (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
          c.kummer.exact (lineBundleClass T L)))
```

## New

```lean
def forgetEvaluatedArrow {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    [HasDerivedCategory.{w₃} H]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {Z : D} (e : F.obj Y ≅ Z)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj X)) ⟶
      ((DerivedCategory.singleFunctor H 0).obj (G.obj Z))⟦(2 : ℤ)⟧ :=
  mapSingleArrow G (2 : ℤ)
    (mapSingleArrow F (2 : ℤ) a ≫
      ((DerivedCategory.singleFunctor D 0).map e.hom)⟦(2 : ℤ)⟧')
```

```lean
def kummerComposite {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] (s : ShortComplex C) (hs : s.ShortExact)
    {X : C} (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :
    (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)⟦(2 : ℤ)⟧ :=
  f ≫ hs.singleδ⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (DerivedCategory C) (1 : ℤ) 1).inv.app
      ((DerivedCategory.singleFunctor C 0).obj s.X₁)
```

```lean
def FiniteChernNormalization {T : Scheme.{u}} (c : Chern l E T) : Prop :=
  ∀ (L : T.Pic) (n : ℕ),
    let a := mapSingleArrow (finiteForget l E T n) (2 : ℤ) (evaluatedChern l E c L n)
    let beta := mapSingleArrow (abEvaluation T n) (2 : ℤ)
      (kummerComposite (C := Ab T)
        (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
        c.kummer.exact (lineBundleClass T L))
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n))⟦(2 : ℤ)⟧') a beta
```

## Users

The direct importers are `Sheaf.Paper.TowerClassFiniteDiagonal`, `Sheaf.Paper.DiagonalTraceChernTwistExistence` and `Sheaf.Paper.DiagonalTowerTraceModels`. All three compiled unchanged against the final item with lcompile.py --all. Their temporary sandbox copies were then removed; no importer is delivered or adapted. The only external textual uses of the generic wrappers are in TowerClassFiniteDiagonal. The explicit result types are definitionally equal to the inferred types; the normalization formula is also definitionally equal to its old formula. No consumer adaptation is expected. The complete downstream inventory follows.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.GeometricConstituentOrbit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.GeometricCurveDiagramDescent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.MarkedGeometricCurveModel` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.PairEigenvalueCurveTest` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.SemisimpleFrobeniusOrbitDescent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.AffineLineAdjunctionAssembly` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompactSupportTowerReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientFreeGenerator` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientOrdinarySquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientPushAction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientRootLineComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientScalarPush` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientSectionAction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedRootProjectionLinear` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompletedSupportedCoefficientTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CompositionComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedCompositorRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalCounitRepresentation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRealizationProperties` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalSystemRecognition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedHomChainRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalBaseSquares` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalClosureLineComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalClosureScalarFrame` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFamilyExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteClosure` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientReference` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientUniformizerReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompleteScalarRestriction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedDiagramRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedFrame` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedLineComplete` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedLineCompleteAux` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedPullbackCompatibility` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedPushSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalCompletionCoefficientTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteArrowEquations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteIntegralEndpoint` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteOrdinaryComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteRootMap` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteScalarSquares` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteTraceChernCriterion` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteTracePresentation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalFlatScalarEndpoint` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalIntegralRootMap` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalNonTorsionBaseChange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalQuotientBaseChange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalScalarCompatibilityTriangle` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalScalarDiagramTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalScalarPullbackCompatibility` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalSupportedScalarSource` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTrace` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceChernTwistExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceComparisonLimitIsos` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceComparisonPartial` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceComparisonPresentation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceCompletedHomBijection` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteChernCohomology` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteIntegralProjection` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteSplitting` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteUnitCohomology` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceGeometricModelExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceIntegrationSystems` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceLimitWitnessExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceOrdinaryLimitEpi` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTracePresentationExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceResultExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceScalarComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceSingleFaithful` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceSources` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceSupportedSourceExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceTwistedSplittingComponents` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalTraceUnitComparisonIso` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerAnnihilator` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerCartierReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerFiniteModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerFiniteNormalization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerScalarFrame` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerScalarSquares` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerTraceChernDegree` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerTraceReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalFiniteCompatibility` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalNormalizedAdjoints` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemAdjoints` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemComponents` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteComposite` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemIso` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemLaws` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionCompletedStrictLimit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionComposition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralDescent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionLimitEquations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalDescent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionReductionDescent` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionReductionLimits` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionStrictLimits` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionSystemCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldExtensionTowers` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemComparisonData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemFiniteOrientation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemHeart` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemNormalizations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemRigidity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldProjectionOriginWitnesses` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTranspose` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTransposeBase` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTransposeCompatibility` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralCoefficientModelComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceMate` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralOrientationShiftedSheafModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.OrderedLineLevelBounds` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.OrderedTowerOrientation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.OrientationScalarTowerTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ProjectiveDiagonalComposition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PulledOrderedLineSingle` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PurityPullbackReductionTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.PurityTowerReductionComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalExceptionalInverseImageExistence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1AmbientComposites` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1AmbientTail` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1CounitInversionCondition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1DiagonalTensor` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1FirstAmbientContraction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1KernelContractions` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1ProjectionNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1SecondAmbientContraction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1SecondPullComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1SecondTraceEquation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1SecondTraceReordering` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1TensorShiftNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1Triangle` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1UnitCounit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalP1UnitInversionCondition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalTatePullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateChartModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateComposition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateFoundations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateProjectionModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluingData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Data` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TateTwistedProjection` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TensorTransposeTowerNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerAdjointCompositorRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerChernPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerChernRealizationPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerCompositorFiniteEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityMate` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerNormalizationPreservation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerOrientationEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1ComparisonsWithLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1CtfData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1DiagonalProjectionFactor` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1DiagonalTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleOriginComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1FiniteAdjunctionAssembly` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1FirstTraceReordering` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1FixedTotalTensor` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1GeometricCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1KernelFiniteComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1KernelScalarData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1KernelScalarNormalization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1KernelSplittingBaseChange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1LevelCtfModel` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1LevelWords` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1OrdinaryPushCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectionLevelComparisons` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectionTraceIdentification` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectiveCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1ProperCtf` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1PushCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1SecondTraceReordering` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelConstruction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelTriangles` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1TensorChainCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1TensorCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1TensorOrdinaryCoordinates` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1TriangleFactorization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1TriangleWords` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1UniformCtfDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerP1UniformPresentation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerPurityAdjointTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedNormalization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeWords` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTraceCanonicalIntegral` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTraceOrientationUniqueness` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerTraceScalarCounit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerUniformEtaleDomains` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerBounds` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerOrigins` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.UniformTowerTensorClosure` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.VerdierIdentityProjection` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.PoincareDuality.ConstructibleSheafBiduality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineChartFormulas` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionNaturality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransitionData` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelContractions` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelTateComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelUnitCounit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedFamily` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarDenseRefinementSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `TargetsCheck` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.Statement` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Additivity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.BaseChangeCoherence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.BorelMoore` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.CompactCohomology` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.CompactPullback` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Correspondence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.CurvePieces` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Dualizing` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FibreCoherence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FibreModel` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPoint` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPointScheme` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Frobenius` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.GenericQuotient` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.HomologyUnit` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTerm` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Main` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ModelExtension` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.OpenPieceCoherence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.OpenSquare` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.PointNormalization` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Product` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCurve` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforward` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.PullbackFamily` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobenius` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusIterate` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Stalk` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.SupportedPairing` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClass` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.TraceFormula.WeilTrace` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | not queried; not adapted | Same signature and normalization formula; no adaptation. |
| `Sheaf.Paper.TowerClassFinite` | not queried; not adapted | Same signature and normalization formula; no adaptation. |

## Status

landed 20261027T021416-L-2768426 2026-10-27 (merge of deliver/W4/Sheaf.Paper.TowerClassFinite)
