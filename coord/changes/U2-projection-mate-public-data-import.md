# moduleObjectProjectionMate public definition import

## Reason

The public definition `moduleObjectProjectionMate` uses
`CategoryTheory.Adjunction.rightAdjointProjectionMap`. The current module system rejects that
public definition when this declaration is available only through private proof imports.
Import its defining source module publicly, as required for a public data definition.
The existing public imports and every existing signature and definition body stay unchanged.

## Old

The existing definition is preserved verbatim:

```lean
noncomputable def moduleObjectProjectionMate
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ f).rightDerivedFunctor.obj A ⊗ B ⟶
      (lowerStar Λ f).rightDerivedFunctor.obj
        (A ⊗ (upperStar Λ f).leftDerivedFunctor.obj B) :=
  (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (moduleObjectDerivedTensorComparison Λ f)).app A).app B

```

No direct public import of the defining module.

## New

```lean
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
```

## Users

All listed consumers see the identical existing declarations, with the source definition API
additionally available. No binder, instance data, target statement or definition is changed.
No consumer needs source adaptation. Claims for unchanged consumers are not changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficients | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficientsData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarCochainNormalization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicRamifiedScalarRealizationData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteTorStability | E5 | Existing interface identical; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | P1 | Existing interface identical; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | J9 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Y3 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing interface identical; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing interface identical; no adaptation. |
| TargetsCheck | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | S6 | Existing interface identical; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | D9 | Existing interface identical; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing interface identical; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Existing interface identical; no adaptation. |

## Status

landed 20261025T043354-L-1710792 2026-10-25 (merge of deliver/U2/Sheaf.Paper.RationalLocalizingProjectionFormula)
