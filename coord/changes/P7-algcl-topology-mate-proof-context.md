# AlgebraicGeometry.ProEtale.algClTopologyMate_hom_bijection proof context

## Reason

Fill both theorem holes using the existing normalized internal scalar-pullback comparison
and the categorical Hom calculation. Keep the derived constructions closed during elaboration.
The local attributes and options affect this file only. No public signature, definition body,
public import, target or mathematical assumption changes.

## Old

```lean
set_option autoImplicit false

```

The bodies of algClTopologyPullbackTheta_isIso and algClTopologyMate_hom_bijection
were `by sorry`.

## New

```lean
set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Profinite.padicAlgClCondensedRing Profinite.continuousMapRingSheaf
set_option allowUnsafeReducibility true
attribute [local reducible] AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.QuotientChange.D
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward

```

After the canonical definitions, the proof also uses local irreducibility of
algClTopologyPullbackSigma, algClTopologyPullbackTheta, algClTopologyDerivedAction,
CondensedRing.derivedUpperStarLowerStarAdjunction,
CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, CondensedRing.upperStar
and Mod.extendScalars. CondensedRing.upperStarComp is also kept closed.

The scalarPullback_mate_isIso, constantModel_pullback, bounded_constantModel_pullback,
restricted_map_bijective, counitMate_hom and counitMate_bijective helpers are private
and proved. Both public theorem bodies use these helpers to avoid unfolding concrete
derived functors during categorical reasoning. The boundedness helper uses a proved constantModel_pullback calculation following
RationalRestrictionGlue and importing the existing public PullbackFiniteConstantLocalModel
theorem. The private source helper is not present in the published build. The first helper uses the already proved
normalized_inverse calculation from NormalizedScalarRestrictionPush and a comparison
supplied by InternalScalarPullbackNormalization. Its section derived categories use the
canonical Grothendieck-abelian construction. All public definitions are unchanged.
The proof also locally closes the theta, sigma, action, derived geometric adjunction
and exact-derived comparison constructions after their definitions; all attributes are local.
The concrete theorem avoids unnecessary coefficient aliases and classical-instance changes.
Local irreducibility also keeps CondensedRing.upperStar, Mod.extendScalars, and the
underlying condensed ring sheaves closed; no reducibility attribute is exported. Scoped maxHeartbeats 800000 covers the generic
scalar normalization proof and the concrete Hom assembly, with the unchanged 60-second
file limit. The private stratification helper is proved and introduces no public declarations
or instances.

## Users

All listed transitive consumers retain the same public API and canonical maps.
The direct theorem consumer is ContinuousQbarExceptionalPreservation; no adaptation is needed.
No consumer is edited, so its claim holder does not affect this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicCommonStageHomTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficients | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicExceptionalCompositorCoefficientsData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicNormalizedPurityLift | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicRamifiedScalarCochainNormalization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicRamifiedScalarRealizationData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceConstruction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ArithmeticRoots | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CartesianSectionAdjointMates | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CartesianSectionData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ChartDiagonalSourceMate | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CondensedHomChainRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ExceptionalReconstructionContext | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteTorStability | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.GeneralHomComparisonCocycles | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.GeometricComparisonData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.GeometricOperations | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.InverseContravariantBidual | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.PodHomChainCtfDomains | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.PointTraceReconstruction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ProperExceptionalRestriction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.ProperProductCounitTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.QbarPerverseSubcategories | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalExceptionalRestriction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalHomScalarTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalTensorSymmetry | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RelativeKunneth | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.RelativeProductInputDomains | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SfBidualityClass | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SfPackageCoefficientDomains | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SfPackageFieldOperationRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SitePerfectRationalBidual | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.SystemScalarProjectionIdentification | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.TraceCorrespondences | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.WeilChosenDualityExchange | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteExceptional | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteScalarMateData | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralDualizing | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.IntegralVerdier | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.RationalOperations | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.RationalVerdier | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarSixCtf | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.ScalarSixDirectImage | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SixFunctors.WeilChosenDualityHom | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.Targets.SmoothPurityQbar | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | Same statements and canonical definitions; no edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | Same statements and canonical definitions; no edit. |
| TargetsCheck | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.PoincareDuality.Poincare | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.PoincareDuality.Verdier | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.SmoothPurity.Defs | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.Statement | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Additivity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Basic | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.BorelMoore | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.CompactCohomology | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.CompactPullback | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Correspondence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.CorrespondencePair | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.CurvePieces | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Dualizing | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FibreCoherence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FibreModel | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FixedPoint | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FixedPointScheme | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Frobenius | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.GenericQuotient | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.HomologyUnit | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.KunnethVerdier | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.LocalTerm | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.LocalTermLocality | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Main | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ModelExtension | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.OpenSquare | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.PointNormalization | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Product | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ProperCompatibility | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ProperCurve | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ProperPushforward | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.PullbackFamily | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobenius | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Stalk | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.Statement | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.SupportedPairing | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.TraceClass | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.WeilBaseChange | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.TraceFormula.WeilTrace | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilSheaf.Curve | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilSheaf.LFunction | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.Rationality | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Same statements and canonical definitions; no edit. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not adapted | Same statements and canonical definitions; no edit. |

## Status

landed 20261025T041235-L-1108777 2026-10-25 (merge of deliver/P7/Sheaf.Paper.AlgClTopologyMateHomBijection)
