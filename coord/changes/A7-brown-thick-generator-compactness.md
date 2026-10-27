# CategoryTheory.brownHypothesesFor_iff_compact_thick_generators

## Reason

Formalize the thick-closure part of the Brown compactness argument. Compactness
only needs to be checked on thick generators; covering every isomorphism class is
unnecessary for this step. Reuse the criterion in the existing representative-family
proof. The disputed arbitrary-field theorem retains its statement and original hole.

## Old

The thick-generator criterion was absent. The representative-family proof was:

```lean
theorem brownHypothesesFor_iff_compact_representatives
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {G : Type*} (g : G → ConstantModelConstructibleFiniteTor Λ X)
    (hG : ∀ C : ConstantModelConstructibleFiniteTor Λ X,
      ∃ i : G, Nonempty (C.obj ≅ (g i).obj)) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ (hL : ∀ i, localizingClosureProEtale Λ X (g i).obj) (i : G),
            IsCompactObject (⟨(g i).obj, hL i⟩ :
              (localizingClosureProEtale Λ X).FullSubcategory) := by
  let L := localizingClosureProEtale Λ X
  constructor
  · intro hB
    obtain ⟨ht, hi, hr, hs, hcop, hc⟩ := (brownHypothesesFor_iff Λ X).mp hB
    refine ⟨ht, hi, hr, hs, hcop, ?_⟩
    intro hL i
    exact hc ⟨(g i).obj, hL i⟩ (g i).property
  · rintro ⟨ht, hi, hr, hs, hcop, hc⟩
    let _ := hcop
    apply (brownHypothesesFor_iff Λ X).mpr
    refine ⟨ht, hi, hr, hs, hcop, ?_⟩
    intro K hK
    obtain ⟨i, ⟨q⟩⟩ := hG ⟨K.obj, hK⟩
    have hL (j : G) : L (g j).obj := fun _ _ hSP ↦ hSP _ (g j).property
    exact compact_of_iso (L.isoMk q) (hc hL i)

```

## New

```lean
theorem brownHypothesesFor_iff_compact_thick_generators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [(localizingClosureProEtale Λ X).IsTriangulated]
    {G : Type*} (E : G → (localizingClosureProEtale Λ X).FullSubcategory)
    (hE : ∀ i, constantModelBoundedConstructible Λ X (E i).obj ∧
      DerivedCategory.finiteTorAmplitude _ (E i).obj)
    (hcover : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      (constantModelBoundedConstructible Λ X K.obj ∧
        DerivedCategory.finiteTorAmplitude _ K.obj) →
      (ObjectProperty.ofObj E ⊔ IsZero).triangEnvelope K) :
    BrownHypothesesFor Λ X ↔
      let S := constantModelBoundedConstructible Λ X ⊓
        fun K ↦ DerivedCategory.finiteTorAmplitude _ K
      S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
          letI := hSums
          ∀ i, IsCompactObject (E i)
```

The representative-family proof now lifts its representatives to L, puts every
constructible object into their thick envelope via an isomorphism, then applies
the new criterion in both directions. Its signature is identical. The criterion
uses the already proved compactObjects_isThick and Mathlib triangEnvelope_le_iff.
A public import of Mathlib.CategoryTheory.Triangulated.Generators supplies the new
statement's thick-envelope notation. A private import of
WeilConjectures.CategoryTheory.CompactObjectsThick supplies the proof only.
No existing declaration, visibility, signature, definition body or instance changes.

## Users

The source census reports 406 transitive importers and no external
named uses of the changed representative criterion. It is still used by the
unchanged finite-field assembly in the item. Existing consumers see identical
interfaces, with the added public Mathlib thick-envelope import. No target
statement or definition changes; no consumer adaptation is required. No module
held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | A7 | New proved criterion; revised representative proof. |
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
| Sheaf.Paper.BrownTowerBoundedTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownTowerGeometricTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownTowerRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.BrownTowerSite | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ChartCounitScalarTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientGammaRepresentatives | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientMapGeometricSquares | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CompactSupportTowerReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedHomChainRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CondensedOpenCounitUnits | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried; no adaptation | Existing interface unchanged. |
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
| Sheaf.Paper.FieldShriekSupportEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemMixed | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FieldShriekSystemTransitions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteCompactSupportDomains | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeCompactComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeCompactScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteFreeScalarProjection | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalIdentityNormalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.GlobalVerdierDualityData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.HomChainPairingNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralAdjunctionBijection | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisonData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.IntegralReconstructionComparisons | Not queried; no adaptation | Existing interface unchanged. |
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
| Sheaf.Paper.NormalizedStageCoefficientCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OpenExceptionalScalarLocality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OpenProEtaleCounitScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.OrderedTateScalarNormalization | Not queried; no adaptation | Existing interface unchanged. |
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
| Sheaf.Paper.PurIntegralRepresentingPair | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurIntegralSupportComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurIntegralSupportComparisonData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.PurityPullbackLevelBounds | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalAffineTensorCalculus | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalP1AmbientComposites | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RawChartScalarCounitPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RestrictionLocal | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ScalarExchangeConstituents | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGamma | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerGluing | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TateTwistedProjection | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TensorHomCoefficientTransposes | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerAdjointCompositorRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerPurityAdjointTransport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.TwistedPullbackTowerDomain | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.VerdierHomChainComposition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.WeilChosenDualityExchange | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.WeilChosenDualityExchangeData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.WeilChosenExchangeConstruction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Paper.WeilChosenTransposeNaturality | Not queried; no adaptation | Existing interface unchanged. |
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
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateData | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried; no adaptation | Existing interface unchanged. |
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
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarSixCtf | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.ScalarSixDirectImage | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SixFunctors.WeilChosenDualityHom | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.PoincareUncurry | Not queried; no adaptation | Existing interface unchanged. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; no adaptation | Existing interface unchanged. |
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

landed 20261025T161838-L-127735 2026-10-25 (merge of deliver/A7/Sheaf.SixFunctorsBasics.BrownHypotheses)
