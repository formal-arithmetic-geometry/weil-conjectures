# AlgebraicGeometry.ProEtale.SpTowerShriek.Geometry.levelAdjunction_eq

## Reason

The original normalization compares only adjunction values by HEq, while their
left and right functors remain separate parameters of the Adjunction type.
After identifying the coefficient sheaves, Lean cannot eliminate that HEq:
`Dependent elimination failed: Failed to solve equation
(proEtaleConstantRingPullback ... ⊣ proEtaleConstantRingPushforward ...) =
((I n).modules ⊣ Qn n)`.
In particular it does not supply the functor equalities needed to transport the
specified evaluation comparisons. The blueprint's constant-coefficient coordinate
identification intends to identify both operations as well as their adjunction.

Replace that field by HEq of the dependent pair of both ordinary functors and
their ordinary adjunction. After coefficient transport it is an ordinary equality
of packages, whose projections give both functor equalities. A proved private
helper localizes this package equality; another proved private helper transports
the two generic evaluation laws. No evaluation law is added as a hypothesis.
This corrects a missing normalization requirement; it is not claimed to follow
from the old HEq field alone. There is no new sorry or selected witness.

This changes the Geometry constructor and its one normalization projection.
All other existing operations, comparisons, definitions and target statements retain
their text. Geometry is an internal proof-interface datum, not a notion in any
Challenge target signature. If the maintainer finds a target definition using it,
its statement review must be reopened as required by AGENTS.md §4.

The data module is unclaimed in the published claim mirror. Textual inspection
of all transitive consumers found no constructor call and no use of the changed
projection except the item being proved. Thus the stronger coordinate witness
must eventually be supplied by strictSystemGeometricRealization (already a named
unfinished theorem), but no existing proof constructing Geometry is overwritten.
The statement and source proof there already require transport along the actual
constant-ring section identifications, which supplies this bundled normalization.

The item now publicly imports SmoothPurityTowerShriekData directly instead of
SmoothPurityTowerShriekLevels. Its sole direct consumer,
TowerCompactSupportProjectionFormula, already publicly imports
SmoothPurityTowerShriekLevels itself. Hence no name used by that consumer is lost.
The item has no need for the tower-shriek existence theorem or its proof imports.

## Old

```lean
  levelAdjunction_eq : ∀ n : ℕ,
    HEq (generic.levelAdjunction n) (proEtaleConstantRingAdjunction (R l E n) f)
```

## New

```lean
  levelAdjunction_eq : ∀ n : ℕ,
    HEq
      (⟨(generic.inverseImage n).modules, generic.levelPush n, generic.levelAdjunction n⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
```

## Users

The table includes every transitive consumer returned by tools/downstream.py,
the changed data module, and the item. Except for the item, all consumer sources
are retained verbatim. No source-library declaration is changed. The repair
changes a proof-interface requirement, so existential construction obligations
using Geometry retain that requirement rather than receiving an arbitrary object.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | F7 | No field projection or constructor use; no source adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | A3 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompactificationScalarData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalBaseSquares | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCompletedDiagramRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCompletedFrame | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalCompletedPushSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalFiniteRootMap | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalIntegralRootMap | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalQuotientBaseChange | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTracePresentationExistence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTraceResultExistence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTraceSingleFaithful | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.DiagonalUniformizerAnnihilator | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | M9 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | W8 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldPuritySystemTranspose | C1 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | E3 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteTateLineUniversal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | J1 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityFiniteLevelProjectionCriterion | H6 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictFiniteWordIdentification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictOpenWordEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictPlusComparisonsRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictPlusEvaluationRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityStrictSystemGeometricRealization | unclaimed | Existing named sorry must construct the corrected canonical coordinate witness; no source edit. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerExchange | H8 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerFibreProjections | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerLocalization | H9 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekData | unclaimed | Repairs the levelAdjunction_eq field; all other fields unchanged. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerChernPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerChernRealizationPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | A4 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerGeometryAdjunctionEvaluation | C4 (this item) | Proves both evaluation laws using the bundled normalization. |
| Sheaf.Paper.TowerIntegralClassPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerLineEvaluationUniversal | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerProjectionDomainEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | Q6 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | A4 | No field projection or constructor use; no source adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | C8 | No field projection or constructor use; no source adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | P2 | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | C4 | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralKernelContractions | D4 | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | Y6 | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedFamily | Z5 | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No field projection or constructor use; no source adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No field projection or constructor use; no source adaptation. |
| TargetsCheck | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.Statement | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No field projection or constructor use; no source adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | No field projection or constructor use; no source adaptation. |

The six additional validation sources are byte-identical copies of the five direct
data consumers and the item's direct consumer; they are removed from the sandbox
after compilation and are not delivered as adaptations.

## Status

landed 20261026T022945-L-508607 2026-10-26 (merge of deliver/C4/Sheaf.Paper.TowerGeometryAdjunctionEvaluation)
