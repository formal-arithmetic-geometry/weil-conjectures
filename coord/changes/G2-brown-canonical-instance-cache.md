# CategoryTheory.brownHypothesesCondensedMonoidal and canonical-instance caches

## Reason

The assigned module exceeded its 60-second single-file compilation limit. Profiling
identified repeated site-size and tensor-structure inference. Cache existing structures
once and supply explicit coefficient arguments in the existing isomorphism-invariance
proof. This is a compilation repair with no theorem claimed proved.

The attempted withdrawal of the false compactness split was rejected by preflight:
restoring the parent's original hole violates the proved-declaration gate. This packet
therefore retains that disputed witness and the parent's proof exactly as on the shared
source. It does not introduce or validate their mathematical assertion.

## Old

There were no named cache abbreviations. Every binder inferred these canonical
structures afresh. The existing coefficient-isomorphism proof used:

```lean
    ⟨h e.symm, h e⟩
```

## New

Six transparent abbreviations name the same canonical structures. Their local instance
attributes avoid repeated inference without exporting any instance attributes. They are
public because a private helper cannot occur in a public definition or signature.

```lean
/-- Cache the canonical monoidal structure on condensed abelian groups.
This is the existing instance, with its site-size witnesses inferred once. -/
noncomputable abbrev brownHypothesesCondensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedMonoidal

/-- Cache the canonical braiding on condensed abelian groups. -/
noncomputable abbrev brownHypothesesCondensedBraided :
    BraidedCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedBraided

/-- Cache the canonical monoidal structure on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory Ab X

attribute [local instance 30000] brownHypothesesSheafMonoidal

/-- Cache the canonical braiding on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafBraided (X : Scheme.{u}) :
    BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab X

attribute [local instance 30000] brownHypothesesSheafBraided

/-- Cache the existing ring-object structure pulled back from condensed coefficients. -/
noncomputable abbrev brownHypothesesCoefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

attribute [local instance 30000] brownHypothesesCoefficientMonObj

/-- Cache the existing closed tensor structure on pro-etale module objects. -/
noncomputable abbrev brownHypothesesModuleMonoidalClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

attribute [local instance 30000] brownHypothesesModuleMonoidalClosed

```

The existing coefficient-isomorphism proof now supplies its coefficient arguments:

```lean
    ⟨fun hB ↦ @h Λ' Λ _ _ _ _ e.symm hB, fun hB ↦ @h Λ Λ' _ _ _ _ e hB⟩
```

No original declaration signature, mathematical definition, source-library declaration,
import or DAG dependency is changed. No extra irreducibility or elaboration options
are added. No data or proof is postponed inside the new abbreviations.

## Users

The full downstream inventory is listed below. All existing signatures and
mathematical definitions are preserved. The six new transparent abbreviations have
local instance attributes only. No downstream module requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientUnitTowerNormalized | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | K2 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | M9 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldExtensionTowers | M3 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemComparison | N1 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorExistence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | K4 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.OrientationScalarTowerTransport | N2 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | S5 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | M4 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerGeometricPurityMate | M2 | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackCofinalModels | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackLineMembership | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackTateReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | C8 | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | R4 | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompatibleComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelContractions | D4 | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | Y6 | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Cache canonical structures and supply explicit proof arguments; all existing statements preserved. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Canonical instance data unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Canonical instance data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Canonical instance data unchanged; no adaptation. |

## Status

landed 20261026T065735-L-3216916 2026-10-26 (merge of deliver/G2/Sheaf.SixFunctorsBasics.BrownHypotheses)
