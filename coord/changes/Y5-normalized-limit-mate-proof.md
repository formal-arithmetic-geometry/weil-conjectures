# AlgebraicGeometry.Scheme.cbcRealizationLimitMap_isIso

## Reason

Prove the existing canonical limit-mate invertibility statement from the normalized
Roos comparison and its derived-unit equation. The added private helpers keep the
unit transports and mate-identification steps explicit. None adds an assumption or
a hole. Two private definitions compose existing canonical unit maps; they do not
choose data from an existence theorem. No existing definition, statement, global
instance, public import or target meaning changes.

The existing scalar/open theorem's essential-image witness is made explicit,
retaining exactly the same isomorphism and mathematical witness. Profiling showed
a roughly 20-second conversion in `cbcRealizationProducts`, so that forgetful
comparison is now proved over arbitrary ring sheaves before specialization. The
entire limit-mate identification is also proved over abstract abelian categories. The
canonical-functor local
irreducibility settings already used by the endpoint module are applied here.

## Old

The existing invertibility theorem's body was `:= by sorry`. There were no
`cbcRealizationCochainUnit*`, `cbcRealizationRoos*`,
`cbcRealizationLimit_cochain_normalized`, `cbcRealizationOrdinaryLimitMate`, or
`cbcRealizationLimit_mate_eq` helpers.

The old essential-image proof was:

```lean
    refine Functor.essImage.ofIso
      ((scalarIso.app (eS.functor.obj M)).symm ≪≫
        (cbcRealizationRes d T).mapIso ((e ≪≫ hS).app M).symm) ?_
    exact LR.obj_mem_essImage _
```

The slow product-preservation step was:

```lean
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T ⋙ G) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf S))
```

## New

The theorem signature is unchanged and its proof is complete. The private unit
constructions are:

```lean
private def cbcRealizationCochainUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  derivedCochainRightUnit (completedTowerLimit T R) (completedRlim T R)
    (completedRlimUnit T R)

private def cbcRealizationRoosUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedRlim T R :=
  (Functor.isoWhiskerRight
    (CategoryTheory.StrictRoosShiftProof.limitModelIso (A := reductionModules T R))
    DerivedCategory.Q).inv ≫ cbcRealizationCochainUnit T R
```

All seven new private theorem helpers are proved from existing APIs. Their
public consumers are the proofs of `cbcRealizationLimitMap_isIso` and
`cbcRealizationProducts`;
no private helper occurs in a public signature or public definition body.

The new essential-image proof gives the same witness directly:

```lean
    exact ⟨(SheafOfModules.RingedOpenScalar.sliceScalars.{t + 1, t, 0}
      (ProEt.mk j) (exchangeScalar d T)).obj (eS.functor.obj M),
      ⟨(scalarIso.app (eS.functor.obj M)).symm ≪≫
        (cbcRealizationRes d T).mapIso ((e ≪≫ hS).app M).symm⟩⟩
```

The namespace uses the following local unfolding context, following the endpoint
module. The attributes cease at the namespace's end and do not affect importers:

```lean
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
```

The scalar/open theorem has its own `section ScalarOpenInvertibility` with:

```lean
attribute [local irreducible] cbcRealizationOpenAdj
```

These attributes prevent large canonical constructions from being unfolded by
unification. No existing public definition body or statement is edited.

The generic forgetful-composite lemma is:

```lean
private theorem cbcRealizationRestrictionForgetsProducts
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (a : R ⟶ S)
    [PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.toSheaf.{t + 1} S)] :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R) := by
  let e : SheafOfModules.restrictScalars.{t + 1} a ⋙ SheafOfModules.toSheaf.{t + 1} R ≅
      SheafOfModules.toSheaf.{t + 1} S :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by rfl)
  exact preservesLimitsOfShape_of_natIso e.symm
```

The specialized step is now:

```lean
    have : PreservesLimitsOfShape (Discrete ℕ) (cbcRealizationRes d T ⋙ G) :=
      cbcRealizationRestrictionForgetsProducts (R := R) (S := S)
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (exchangeScalar d T))
```

The unit-conversion helper takes abstract categories, inverse-limit additivity,
the two cochain units and their pointwise equalities with the universal units.
Its proof is the same Roos-normalization equation followed by these equalities;
the sheaf specialization supplies the already proved unit identities.

The following style-linter settings follow `ExactProductFunctorStrictLimit` and
avoid repeatedly traversing the dependent comparison interfaces:

```lean
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
```

The complete mate-identification helper now also takes abstract categories and
cochain units. Its ordinary projection calculation is isolated in the proved
`cbcRealizationOrdinaryLimitMate`, including the categorical identity-composition
step before invoking the canonical limit-comparison projection equation. The
public theorem specializes this identity to the completed coefficient categories.
This avoids rechecking the projection argument through the concrete sheaf models.

The existing evaluation section additionally keeps its two large constructions
abstract during elaboration, as other ringed-pullback proofs do:

```lean
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
```

Proof checking is scheduled sequentially before the final axiom scan:

```lean
set_option Elab.async false
```

This changes scheduling only and leaves full proof and axiom checks enabled. The
complete instrumented module compiled in 43.7 seconds with this option.

The file still undergoes full kernel checking. No diagnostic option, custom tactic,
compile-time limit change or new `respectTransparency` setting is delivered.

The added imports use `import all` solely for existing proved private proof APIs:

```lean
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import all Sheaf.CategoryTheory.StrictRoosShiftLocalization
import all Sheaf.Paper.NormalizedLimitSquareCoherence
import all Sheaf.Paper.ExactProductFunctorStrictLimit
import all Sheaf.Paper.StrictTowerExchangeMateNormalization
import all Sheaf.Paper.RingedOpenScalarLimitCoherence
```

## Users

The following transitive consumers are listed by `tools/downstream.py` for the
item. Every existing exported signature, definition and public import is retained,
and no consumer requires adaptation. No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | C3 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompactificationScalarData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompletedOpenExchangeLimitNormalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompletedOpenFiniteTransposeCoherence | M2 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompletedOpenScalarLimitSquare | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateTranspose | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | H5 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | P9 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurIntegralCompletedCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurIntegralGeometricInputNormalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurIntegralStrictCalculus | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurIntegralStrictReduction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurIntegralTotalUnitEquation | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | J1 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | U2 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | F2 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | G3 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | Q6 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | A4 | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | C4 | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | X6 | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public API and meanings; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization (3) | unclaimed | Same public API and meanings; no adaptation. |

## Status

landed 20261026T024251-L-654230 2026-10-26 (merge of deliver/Y5/Sheaf.Paper.CompleteProetaleStrictTowerRealization)
