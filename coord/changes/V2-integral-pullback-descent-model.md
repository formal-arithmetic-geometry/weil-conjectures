# WeilConjectures.integralDerivedPullback and integralDerivedPullbackComparison

## Reason

Kernel profiling of the assigned item identified the normalization API's nested
existential choices as an expensive conversion: accessing its universal property
required unfolding the functor and comparison through the large well-definedness
statement. Package the existing functor, comparison and universal property in
`IntegralPullbackDescent`, following the existing `IntegralCompletedTensorDescent`
record in the same module. The concrete record uses precisely the old two choices,
without making a new choice. Its universal field is proved by the existing
`integralOperationsWellDefined` theorem. Both existing definitions now project
these exact old values from the record and remain definitionally equal to their
previous bodies. No mathematical hypothesis, conclusion or object changes.

`Sheaf.Paper.IntegralDerivedOperations` is unclaimed in the current local claim
records. It has zero holes before and after the change. No source module under
`WeilConjectures/` changes. The original public imports and existing declaration
signatures stay verbatim. The new record and constructor are public so the parent
proof can use the normalization API without opening its construction. No global
irreducibility attribute is introduced.

The pullback section locally prefers `integralTowerHasDerivedCategory` at priority
3000, matching the theorem that supplies its data. The scope contains only the new
`IntegralPullbackDescent` and `integralPullbackDescent`; it closes before the existing
`integralDerivedPullback` and `integralDerivedPullbackComparison`, so their elaborated
types keep the published instance `integralOperationsCommHasDerivedCategory` on X
(reviewer fix, 2026-10-26: inside the scope both types had switched to
`integralTowerHasDerivedCategory`, a signature change of the elaborated terms). The
tensor and internal-Hom declarations are outside it too. No global instance priority
changes.

## Old

```lean
noncomputable def integralDerivedPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l E X) :=
  (integralOperationsWellDefined l E f X).2.2.choose

noncomputable def integralDerivedPullbackComparison {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      integralOperationsPullbackOnGood l E f :=
  (integralOperationsWellDefined l E f X).2.2.choose_spec.choose
```

## New

```lean
structure IntegralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) where
  functor : DerivedCategory (integralTowerModules l E Y) ⥤
    DerivedCategory (integralTowerModules l E X)
  comparison : integralOperationsGoodLocalization l E Y ⋙ functor ≅
    integralOperationsPullbackOnGood l E f
  universal : ∀ (G : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l E X))
    (e : integralOperationsGoodLocalization l E Y ⋙ G ≅
      integralOperationsPullbackOnGood l E f),
    ∃! i : functor ≅ G,
      Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) i ≪≫ e = comparison

noncomputable def integralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) : IntegralPullbackDescent l E f where
  functor := (integralOperationsWellDefined l E f X).2.2.choose
  comparison := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.1

noncomputable def integralDerivedPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l E X) :=
  (integralPullbackDescent l E f).functor

noncomputable def integralDerivedPullbackComparison {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      integralOperationsPullbackOnGood l E f :=
  (integralPullbackDescent l E f).comparison
```

## Users

A read-only textual audit of the current source and delivery overlay lists 245 consumers
of the existing and packaged pullback names.
Each retains the same statement, since reducing the new record projections gives
the exact old functor and comparison. Thus none becomes weaker, stronger or
different. No existing consumer proof requires adaptation. The item uses the new universal
field in its newly written proof. The original module and the item with
all five local prerequisites passed their single-file checks. The assembled item also
passed in 54.7 seconds; delivery repeats clean compilation after removing profiling options.
Since these definitions occur in target dependencies, the usual independent
statement review must confirm their unchanged mathematical values.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceFiniteness` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AllStageCtfPullbackUnit` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.AutomorphismSquareRationalScalar` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | M1 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CanonicalTateComparisons` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ClopenProjectiveChartCommonRefinement` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ClopenSystemIntegralRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionReduction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealizationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientFamilyTransportModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientTransportExpressions` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | G8 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | E4 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedUnitPullbackData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.CompletedUnitPullbackTower` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | D4 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | G2 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | B8 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.EffectiveQuotientModelDescent` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ExplicitScalarConeWordCoordinates` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdCompletedCompositorNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FieldExtensionSourceNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionCoefficientGeometry` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionGeometricArrows` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrameworkPbcIntegralComparisonLaws` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackComparisonData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | V4 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IdentityCompactificationLimitComparisons` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralAmbientOperationModels` | S7 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralComparisonPullbackRealizationShifts` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralDerivedOperations` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralDerivedPullbackLinear` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralImmersionPullbackNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralImmersionPullbackNormalizationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralImmersionShiftCompatibility` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralObjectPullbackLine` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralOperationsScalarExtension` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | P1 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparisonData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCounitProjection` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackRoosFiniteTower` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackShiftCoordinates` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackSignedShift` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralSemilinearGermSquare` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralStratumChartRestrictions` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsFunctorial` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.InverseImagePullbackComparisonDerived` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportRationalScalar` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackRationalExact` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackRawStage` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackScalarShift` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackTExactCoefficients` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.IteratedReturnTransportScalarCalculus` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NormalizedCompletedOperationModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralMixedCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralScalarCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.OpenCompletedRestrictionIdentification` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.OrdinaryIntegralPullbackConstruction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PodCompletionReindexModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PodReindexingDerivedComparisons` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | G1 | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointAutomorphismDerivedTransportInverse` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointFrobeniusNormalizationDefinitions` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointIdentityExchangeRecipe` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointPullbackConeLocalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointPullbackRepresentativeDiagram` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PointTransportResolutionCancellation` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PrimitiveQuotientPullbackModelExistence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PrimitiveQuotientRealizationsUnique` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ProperIntegralOrdinaryData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ProperIntegralOrdinaryInputs` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ProperIntegralStrictModelComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PullbackCommonStrictTowerModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.PurityKappaStages` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RationalRestrictionComparisonCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RealizedPullbackComparisons` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.RelativeProductFactors` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfFrameworkThetaShiftCompatibility` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfIntegralClosedKernelRoos` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfIntegralKernelRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfIntegralOpenKernelCompactSupport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfIntegralOrdinaryRecollementRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SitePerfectComplex` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SourceSectionIdentityModel` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SupportedTorReductionPropagation` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedNormalization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTraceCanonicalIntegral` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTraceOrientationUniqueness` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TowerTraceScalarCounit` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TraceBoundedQuotientStalkRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionTower` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlFiniteIntegralFibreReconstruction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlOpenCompactSupportRestriction` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.CompletedSystemPullbackPreservation` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquare` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherenceData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorExchangeRealization` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.PrimitiveQuotientAugmentations` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.SixFunctors.TensorAdjunctionReductionSquares` | unclaimed | Same signatures and definitionally equal values; no adaptation. |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IntegralComparisonCounitCharacterization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent` | V2 | Retains its statement; its proof uses the normalized record and re-exported models. |
| `Sheaf.TraceFormula.IsomorphismQuotientRoosComparison` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.IsomorphismStrictQuotientMultiplication` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.LocalNormalizationStrictRealization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |
| `Sheaf.TraceFormula.StrictQuotientCompletionRealization` | unclaimed | Delivered comparison module; statements use the same recorded constructions. |

## Status

landed 20261026T092852-L-3475163 2026-10-26 (merge of deliver/V2/Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent)
