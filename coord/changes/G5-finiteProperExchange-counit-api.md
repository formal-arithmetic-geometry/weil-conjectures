# AlgebraicGeometry.ProEtale.CondensedRing.finiteProperExchange

## Reason

Kernel checking the item repeatedly timed out while converting `eqToIso` equality
transport inside the expanded derived pullback square. Name that exact square
`finitePullbackSquare` and implement its middle equality transport by equality
induction, as the ordinary `ProEtale.leftDerivedUpperStarCongr` already does.
The explicit construction `finitePullbackCongr` is proved equal to the old
`eqToIso (congrArg ... h)` by `finitePullbackCongr_eqToIso`. Therefore the original
canonical square and exchange map are equal, with no new choice or hypothesis.
`finiteProperExchange_eq_mate`, proved by reflexivity, supplies the defining-mate API.

This is an interface repair in an unclaimed `Sheaf` module. Existing signatures,
attributes and public imports stay unchanged, and the adopted source library is
preserved in full. Target statements retain the same meaning; the definition change
is submitted for independent review of targets which use it. No consumer statement
becomes weaker, stronger or different. Profiling the original equality transport
showed a kernel deterministic timeout after 80.9 seconds; the equality-induction
version checks the item in 54 seconds, including four seconds of kernel checking.

## Old

```lean
@[no_expose] noncomputable def finiteProperExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  (mateEquiv
    (G := (upperStar Λ g).leftDerivedFunctor)
    (H := (upperStar Λ g').leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (TwoSquare.mk _ _ _ _ (((leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (congrArg (fun (f : X' ⟶ Y) ↦ (upperStar Λ f).leftDerivedFunctor) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ g' p).hom))).natTrans
```

## New

```lean
/-- Equality transport for internal derived inverse images, by equality induction.
Source: transport of the published derived inverse-image functor
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finitePullbackCongr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (upperStar Λ f).leftDerivedFunctor ≅ (upperStar Λ g).leftDerivedFunctor :=
  h ▸ Iso.refl _

/-- Equality induction normalizes reflexive pullback transport.
Source: the reflexivity equation for equality transport
(blueprint: def-sfb-finite-proper-exchange). -/
@[simp] theorem finitePullbackCongr_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finitePullbackCongr Λ (rfl : f = f) = Iso.refl _ := by
  rfl

/-- Equality-induction transport is the original equality-to-isomorphism transport.
Source: equality induction for the published derived inverse-image functor
(blueprint: def-sfb-finite-proper-exchange). -/
theorem finitePullbackCongr_eqToIso
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    finitePullbackCongr Λ h =
      eqToIso (congrArg (fun (k : X ⟶ Y) ↦ (upperStar Λ k).leftDerivedFunctor) h) := by
  cases h
  rfl

/-- The canonical internal derived inverse-image square, kept as a named isomorphism.
Source: the published pullback compositors and equality transport
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finitePullbackSquare
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (upperStar Λ g).leftDerivedFunctor ⋙ (upperStar Λ p').leftDerivedFunctor ≅
      (upperStar Λ p).leftDerivedFunctor ⋙ (upperStar Λ g').leftDerivedFunctor :=
  (leftDerivedUpperStarComp Λ p' g).symm ≪≫
    finitePullbackCongr Λ sq.w.symm ≪≫
    leftDerivedUpperStarComp Λ g' p

/-- The unit-square-counit mate of the canonical derived pullback compositor.
Source: blueprint proper-base-change-finite, clause (2), and the canonical mate convention.
(blueprint: def-sfb-finite-proper-exchange). -/
@[no_expose] noncomputable def finiteProperExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  (mateEquiv
    (G := (upperStar Λ g).leftDerivedFunctor)
    (H := (upperStar Λ g').leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (TwoSquare.mk _ _ _ _ (finitePullbackSquare Λ sq).hom)).natTrans

/-- The canonical exchange is its defining mate, without exposing the construction.
Source: the definition of the unit-square-counit exchange
(blueprint: def-sfb-finite-proper-exchange). -/
theorem finiteProperExchange_eq_mate
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    finiteProperExchange Λ sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
        (derivedUpperStarLowerStarAdjunction Λ p')
        (TwoSquare.mk _ _ _ _ (finitePullbackSquare Λ sq).hom)).natTrans := by
  rfl
```

The named square has real, explicit data. Equality-induction transport and its
reflexivity equation are exactly the ordinary pullback API's convention.
The private proof import `import all Sheaf.Paper.FiniteProperExchange` in the item
allows unfolding the named square just in the composition-cube proof; it does not
expose that body to the item's importers.

## Users

`tools/downstream.py Sheaf.Paper.FiniteProperExchange --uses finiteProperExchange`
reports 565 transitive downstream modules and three textual users. The table
lists their union, including the modified module; holder status was read from
the current claim records.
All functor endpoints and existing signatures are identical. Equality induction
proves the new transport is the old transport, so consumer statements keep their
meaning and no consumer requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | G2 | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | F7 | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | F8 | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | B3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CompositionComparisons | B4 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | A6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | C3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | M9 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemSquare | S2 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F8 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteCoefficientExchangeEncoding | G5 | Use the square, equality-induction transport and mate API. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | F1 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | K9 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | W9 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteProperExchange | unclaimed | Name the canonical square; prove transport and mate equations. |
| Sheaf.Paper.FiniteProperLocalizing | Y6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | S3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.GeometricGeneratorProjectionDevissage | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | S6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | N4 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | U6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MateOpenCompactSupportExchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MateOpenProperRestrictionIso | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MateOpenProperSupport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.P1CounitScalar | M1 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | G1 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | T2 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | V2 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | H8 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProperAlgClComparisonDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | B3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | A5 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | T9 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | Q4 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | F9 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | P1 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | N3 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | C8 | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | P2 | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | K5 | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.CompactSupportRefinementBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | F5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | D6 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | T5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | C9 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | Z5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | X2 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | T7 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | D5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | B5 | Same canonical exchange; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | R3 | Same canonical exchange; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same canonical exchange; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same canonical exchange; no adaptation. |
| TargetsCheck | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same canonical exchange; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Same canonical exchange; no adaptation. |

The definition node gains the named square and proved API declarations in
`lean.declarations`; its statement and mathematical construction stay unchanged.

## Status

landed 20261025T204629-L-2985599 2026-10-25 (merge of deliver/G5/Sheaf.Paper.FiniteCoefficientExchangeEncoding)
