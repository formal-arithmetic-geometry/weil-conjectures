# WeilConjectures.CompletedOperations primitive model declarations

## Reason

The construction of simultaneous normalized quotient/Roos models is independent of
recursive finite expressions. Move the existing declarations Models, tensor, unit,
tensorRealization, tensorComparison and pullbackComparison verbatim to
Sheaf.Paper.NormalizedCompletedOperationModels and publicly re-export them from
their original module. This permits the primitive construction theorem to be a
separate proof dependency without an import cycle. No data is chosen from this
existence theorem in a definition; the final theorem eliminates it propositionally.

## Old

The following declarations lived in Sheaf.Paper.CompletedOperationTowerSubstitution:

```lean
/-- Compatible presentations of the *specified* operations. The tensor structures
are normalized on K-flat total complexes by RingedSiteDualityModel; the reduction
calculus fixes every quotient map and both adjunction projections. Completion's
comparison is pinned by the actual quotient/Roos augmentation. Pullback's
comparison is pinned on every simultaneous quotient presentation, not chosen
separately on evaluated objects.
Source: node proof steps 1, 4--5; Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- These are presentations of the same system closed tensor. -/
  system_closed : ∀ a : S, (system a).closed = (calculus a).systemClosed
  /-- The integral tensor is the recorded ordinary tensor used by completion. -/
  integral_closed : ∀ a : S,
    (calculus a).integralClosed = (IntegralOnSlice.duality l E (W a) none).closed
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

/-- The system tensor in the fixed canonical total-complex presentation.
Source: node proof steps 1--2 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensor (a : S) := (M.system a).closed.tensor

/-- The coefficient unit system B_n[0], including its actual quotient transitions.
Source: node proof steps 3 and 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def unit (a : S) : coefficientSequenceDerived l E (W a) :=
  ringedSiteDualityUnit.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))

/-- The defining quotient-limit tensor realization. Each factor is fixed by the
reduction tensor model, closed-tensor presentation, or completion augmentation.
Source: node proof step 5 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (eqToIso (congrArg CoefficientClosedStructure.tensor (M.integral_closed a).symm))
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (eqToIso (congrArg CoefficientClosedStructure.tensor (M.system_closed a).symm)))
      (coefficientSequenceLimit l E (W a))

/-- The primitive tensor comparison is L(T(e_A,e_N)), after its defining realization.
This is a formula using the coherent counit, before any invertibility assertion.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorComparison (a : S) (A N : coefficientSequenceDerived l E (W a)) :
    (IntegralOnSlice.completedTensor l E (W a) none).obj
        ((coefficientSequenceLimit l E (W a)).obj A,
         (coefficientSequenceLimit l E (W a)).obj N) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((tensor l E M a).obj (A, N)) :=
  (tensorRealization l E M a).hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((tensor l E M a).map (Prod.mkHom
        ((M.calculus a).adjunction.counit.app A) ((M.calculus a).adjunction.counit.app N)))

/-- The primitive pullback comparison is L(F(e_C)), after quotient-model realization.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def pullbackComparison {a b : S} (f : W a ⟶ W b)
    (C : coefficientSequenceDerived l E (W b)) :
    (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E (W b)).obj C) ⟶
      (coefficientSequenceLimit l E (W a)).obj
        ((integralComparisonDerivedSequencePullback l E f).obj C) :=
  (M.pullback f).realization.hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((integralComparisonDerivedSequencePullback l E f).map
        ((M.calculus b).adjunction.counit.app C))

```

## New

The declarations above are verbatim in
Sheaf.Paper.NormalizedCompletedOperationModels, with unchanged namespaces,
universes, bodies, fields, visibility and attributes. Their original module adds:

```lean
public import Sheaf.Paper.NormalizedCompletedOperationModels
```

The new module also states PrimitiveLaws (effective coherent counit and closure of
normalization for unit, tensor and pullback) and normalizedCompletedOperationModels.
The original theorem type and every remaining declaration are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Only finite-coefficient monoidal units; identical public re-export, no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | projectionTensorActionIsoType uses AffineSpacePurity.tensor, not CompletedOperations.tensor; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Uses its own AffineZeroPurity.unit, the degree-zero finite coefficient sheaf; the moved declarations remain identical through public re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Uses its own finite-coefficient tensor definition; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Uses the finite-coefficient tensor of AffineSpacePurityComparison; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Uses AffineZeroPurity.unit and AffineSpacePurity.tensor for the finite Tate target; identical moved declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Uses AffineZeroPurity.unit and AffineSpacePurity.tensor in finite zero-section purity; identical moved declarations through public re-export; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | F5 | Publicly re-exports the identical primitives and uses them in the proved assembly. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | E9 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | projectionSourceRaw uses AffineSpacePurity.tensor, not CompletedOperations.tensor; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | G7 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | V9 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | The unit matches are local binders in the two Thom tensor equations; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C2 | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | A2 | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Uses finite-field localizing compactness and no moved declaration directly; identical primitive visibility through public re-export; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Identical declarations through public re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Identical declarations through public re-export; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical declarations through public re-export; no adaptation. |

The Users table was refreshed against the current source import graph on 2026-10-22
for the return at head 6785a854815. It includes all 703 current transitive
importers, the changed item itself, and all previously recorded consumers
(867 rows total). The three added modules have no current claim; existing holder
entries are retained from the preceding inventory.
The six moved declarations, including their bodies, remain identical through
public re-export. The original theorem signature is unchanged.

The returned consumer Sheaf.Paper.VectorBundleThom has been read in full.
Its two short-name `unit` occurrences are parameters of
VectorBundleThomTensorEquation and VectorBundleTraceTensorEquation, used in
`HEq m unit`. They do not refer to CompletedOperations.unit. Its declarations
need no adaptation. The current downstream scan also adds VectorBundleThomMaps,
VectorBundleThomProduct, AffineSpacePurityComparison and AffineSpacePurityComposition.
The last two use their own finite-coefficient tensor, distinct from the moved
CompletedOperations.tensor. The Thom maps and product retain identical primitive
visibility through the original module's public re-export.

Previously returned consumers remain recorded: OrientationFiniteReductionTwists,
SixFunctorOrientationDatum, SixFunctorOrientationFiniteFamily,
SixFunctorOrientationHigherPair, VectorIntegrationSiteComparison and
PerAdicNormalizedFibreComparisons (all under Sheaf.Paper). Their unit/tensor
matches belong to other interfaces. No target statement or definition changes meaning.

The return at head 6785a854815 passed independent review but failed landing
because AffineDiagonalTensorCoordinates and ProjectionPurityAgreement were
missing from this table. Both modules open AlgebraicGeometry.ProEtale.AffineSpacePurity
inside WeilConjectures.PurityFiniteSetting. The short-name tensor in
projectionTensorActionIsoType (AffineDiagonalTensorCoordinates) and
projectionSourceRaw (ProjectionPurityAgreement) is that finite-coefficient tensor,
not WeilConjectures.CompletedOperations.tensor. Neither module mentions any of
the other five moved declarations in code. Their signatures and definitions
therefore keep the same meaning; no Lean adaptation is necessary.
AffineDiagonalTateCoordinates is also now a downstream module, so it is recorded:
its unit notation and unit comparisons are the finite-coefficient monoidal units,
with no reference to the moved CompletedOperations.unit. All three source modules
were inspected for this repair. The current downstream inventory has no missing
Users row. The delivery tool creates the rebased commit on current sheaf-dag.

The return at head 305fcaa044e identified three further missing Users rows:
AffineSpaceCoordinateBoundaries, AffineSpaceThomMap and AffineSpaceZeroSectionPurity
(all under Sheaf.Paper). They define or use AffineZeroPurity.unit; the latter
is the degree-zero finite coefficient sheaf. Their tensor occurrences are
AffineSpacePurity.tensor on finite coefficients. These are separate declarations
from the moved CompletedOperations.unit and CompletedOperations.tensor.
All three sources were inspected; no signature, definition or proof needs adaptation.
Also inspected and recorded the newly downstream
Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness, which uses localizing
compactness and no moved primitive directly. No group currently claims these
four modules. The refreshed table retains all earlier rows and now contains
871 consumers, covering all 705 current transitive importers and the item itself.
The moved primitive declaration block and assigned theorem signature were checked
verbatim against current source. Only this change record and report were edited
for this return; deliver3.py rebases the retained Lean and nodes.

## Status

landed 20261022T021031-L-164224 2026-10-22 (merge of deliver/F5/Sheaf.Paper.CompletedOperationTowerSubstitution)
