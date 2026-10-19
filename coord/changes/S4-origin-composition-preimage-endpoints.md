# originCompositionAmbient, originComposition and originCompactSupportId

## Reason

Make the source and target of three fully faithful `preimageIso` applications explicit.
This prevents Lean's elaborator from searching through the large comparison functors
while checking the newly completed coherence proofs. The endpoint arguments are exactly
those previously inferred from the unchanged result types. No construction is replaced:
the same fully faithful preimage of the same natural isomorphism is retained. Local
irreducibility is used only inside this file's proofs. All public signatures, visibility
and public imports stay identical.

## Old

```lean
def originCompositionAmbient :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (originCompositionModel A f g)

def originComposition :
    originCompactSupport A f ⋙ originCompactSupport A g ≅ originCompactSupport A (f ≫ g) :=
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  (H.whiskeringRight _).preimageIso (originCompositionAmbient A f g)

def originCompactSupportId (T : Scheme.{u}) :
    originCompactSupport A (𝟙 T) ≅ 𝟭 _ :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  (H.whiskeringRight _).preimageIso ambient
```

## New

```lean
def originCompositionAmbient :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ≅
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g) :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso
    (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (originCompositionModel A f g)

def originComposition :
    originCompactSupport A f ⋙ originCompactSupport A g ≅ originCompactSupport A (f ≫ g) :=
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  (H.whiskeringRight _).preimageIso
    (X := originCompactSupport A f ⋙ originCompactSupport A g)
    (Y := originCompactSupport A (f ≫ g)) (originCompositionAmbient A f g)

def originCompactSupportId (T : Scheme.{u}) :
    originCompactSupport A (𝟙 T) ≅ 𝟭 _ :=
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) T
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory
  let model := compactSupportSiteComparison A (HasCompactification.compactification (𝟙 T)) ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (𝟙 T)).symm ν ≪≫
    Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekPlusId A T)
      (DerivedCategory.Plus.ι ⋙ ν)
  let ambient : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 T) ≅
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).ι :=
    (Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso model
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) T).fullyFaithfulι
  (H.whiskeringRight _).preimageIso
    (X := originCompactSupport A (𝟙 T)) (Y := 𝟭 _) ambient
```

## Users

The table includes every transitive importer reported by `tools/downstream.py` on the
current shared sources, even when it does not mention these three declarations.
The changes merely spell out implicit arguments, so old and new constructions have the
same elaborated meaning. No consumer requires adaptation, and no target meaning changes.
The holder column records the read-only coordination query at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | S4 | Item: four proofs completed; explicit inferred endpoints. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin | A2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | X5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CompactSupportSiteCoherence | U2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CompositeIntegrationCounit | J7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | K6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | U1 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | D7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | H4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.StandingExceptionalComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceExceptionalAdmissibility | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | U6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Unchanged signatures and canonical constructions; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signatures and canonical constructions; no adaptation. |

## Status

landed 20261019T231337-L-576271 2026-10-19 (merge of deliver/S4/Sheaf.Paper.CanonicalOriginCompactSupportComposition)
