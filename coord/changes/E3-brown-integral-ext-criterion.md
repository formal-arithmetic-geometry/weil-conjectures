# CategoryTheory.brownHypothesesFor_padicIntegers_iff_ext_bounded

## Reason

Identify the exact missing Ext-bound condition for integral Brown compactness over an
arbitrary positive-characteristic field. Prove both directions from existing declarations,
then use the criterion and the finite-field Ext bound for integral coefficients in the
existing supported finite-field assembly. Transport compactness over the given coefficient
isomorphism using the existing canonical ambient Hom-map comparison lemmas.

All existing declaration signatures, visibility, public imports and non-theorem bodies
are preserved. The disputed arbitrary-field theorem and its original sorry are unchanged.
No target statement or target definition changes, and no consumer adaptation is needed.

## Old

The criterion was absent. The private finite-field assembly chose a small skeleton and
used the finite-field representative compactness theorem for every coefficient case.
The existing finite-field and arbitrary-field theorem signatures are unchanged.

## New

```lean
theorem brownHypothesesFor_padicIntegers_iff_ext_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X ↔
      ∀ C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
        ∃ d : ℤ,
          ∀ N : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X,
            ∀ q : ℤ, d < q →
              Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C.obj) ⟶
                ((DerivedCategory.singleFunctor _ 0).obj N.obj)⟦q⟧)
```

A proved private helper, compactness_of_brown_coefficientIso, transfers the compactness
clause from a Brown bundle across an isomorphism of condensed coefficient rings.
It expresses compactness as the ambient canonical Hom direct-sum comparison, transports
that comparison through the existing derived coefficient equivalence, and reflects it
along the full localizing inclusion. It makes no arbitrary-field compactness assertion.

The private finite-field assembly first handles coefficients isomorphic to O_E by
applying the new criterion with integralConstructibleExt. The remaining cases retain
the original skeleton argument. New imports are proof-only; BrownHypothesesSmall and
BrownHypothesesGeneration are imported with `all` only to use their proved private helpers.

## Users

The prescribed downstream census found 502 transitive modules and zero existing
uses of the new criterion. Every original declaration signature and non-theorem body
was checked with tools/stage3_delivery.py's source parser. No downstream module requires
adaptation: the only existing proof changed is the private finite-field assembly.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | E3 | New proved criterion and private transport helper; private finite-field proof updated. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AdmissibleVerdierExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AffineCounitScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ArithmeticRoots | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ChartCounitScalarTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CompactSupportTowerReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CompositionComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedHomChainRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCoefficientModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitUnits | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenUnitComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleCtfChartDomain | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.EtaleSumCounitScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ExceptionalRealizationNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionContext | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemComponents | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemIso | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldExceptionalSystemLaws | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldProjectionOpenSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldProjectionProperSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldProjectionSystemData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldProjectionSystemSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldProjectionTensorConstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSupportEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemCocycle | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemMixed | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteCompactSupportDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalIdentityNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalVerdierDualityData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralCompositorLimitRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralTowerImageReconstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.MateOpenCompactSupportExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.MateOpenProperRestrictionIso | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.MateOpenRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.MateOpenRestrictionMaps | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.NonrationalCompositionSeed | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OpenExceptionalScalarLocality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OpenProEtaleCounitScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedLineLevelBounds | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedTateScalarNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedTowerOrientation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrientationGroundFieldRetagging | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.P1CounitScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.P1SplittingScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PodCtfAdjunctions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PodCtfPairingMaps | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PodHomChainCounitFormula | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PodHomChainCtfDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PodHomChainUncurriedTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ProjectionFiniteReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurAdicReconstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityFiniteReductionTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityPullbackReductionTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityTowerReductionComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalAffineTensorCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalP1AmbientComposites | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalP1KernelContractions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalP1Triangle | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalP1UnitCounit | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RawChartScalarCounitPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RestrictionLocal | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBound | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerChartData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGammaData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluing | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluingData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Data | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TateTwistedProjection | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TensorTransposeTowerNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerAdjointCompositorRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerNormalizationPreservation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1CtfData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1DiagonalTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1FirstTraceReordering | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1FixedTotalTensor | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1GeometricCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1KernelScalarData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1LevelCtfModel | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1LevelWords | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1ProperCtf | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1PushCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1SecondTraceReordering | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1SingleLevelData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1TensorCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1TriangleFactorization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1TriangleWords | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1UniformCtfDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerP1UniformPresentation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorAdjointDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorTransposeWords | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerUniformEtaleDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackReductionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackReductionTower | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackTowerBounds | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomain | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.UniformTowerTensorClosure | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.Reduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionOrientation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralKernelContractions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarSixDirectImage | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.PoincareUncurry | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not queried; no adaptation | Existing interface unchanged. |
| TargetsCheck | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.PoincareDuality.Verdier | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.SmoothPurity.Defs | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.Statement | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Additivity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Basic | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.CoefficientMorphism | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.CompactCohomology | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.CompactPullback | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Correspondence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.CorrespondencePair | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.CurvePieces | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Dualizing | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FibreCoherence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FibreModel | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FixedPoint | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FixedPointScheme | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Frobenius | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.GenericQuotient | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.HomologyUnit | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.KunnethVerdier | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.LefschetzVerdier | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.LocalTermLocality | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Main | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ModelExtension | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.OpenSquare | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.PointNormalization | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Product | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ProperCompatibility | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ProperCurve | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ProperPushforward | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.PullbackFamily | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobenius | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Stalk | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.Statement | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.SupportedPairing | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.TraceClass | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.WeilBaseChange | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.TraceFormula.WeilTrace | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilSheaf.Curve | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilSheaf.LFunction | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.Examples | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.Rationality | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.Weights | Not queried; no adaptation | Existing interface unchanged. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | Not queried; no adaptation | Existing interface unchanged. |

## Status

landed 20261025T205918-L-3401770 2026-10-25 (merge of deliver/E3/Sheaf.SixFunctorsBasics.BrownHypotheses)
