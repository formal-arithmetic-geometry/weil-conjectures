# CategoryTheory.brownHypothesesFor_iff_compact_of_admissible

## Reason

The human removed the all-continuous algebraic-closure alternative from admissibility
on 2026-10-25. The actual six-case predicate is now exactly the range covered by the
smallness theorem. Consequently thickness and essential smallness hold over every
finite-type field scheme, independently of the disputed compactness assertion.
Factor this argument out of the private finite-field specialization and prove that
Brown's bundle is equivalent to its objectwise compactness clause in this setting.

This is a proved reduction criterion, not a proof or a decomposition by new holes of
the arbitrary-field Brown assertion. That original theorem remains disputed and sorry.

## Old

The new public criterion did not exist. The old private finite-field specialization
contained the complete coefficient-by-coefficient thickness and size argument inline,
then used brownHypothesesFor_iff to assemble these clauses with compactness.

Every existing declaration signature, visibility, public import and definition body
is retained verbatim. No source-library module changes. The already-proved localizingClosure_generatingFamily
also receives its missing JSON node, at the id already cited by the item and formal
criterion; its declaration and proof are unchanged.

## New

```lean
theorem brownHypothesesFor_iff_compact_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ r : ℕ, ∀ a : A, (ℓ ^ r) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    BrownHypothesesFor Λ X ↔
      ∃ hSums : HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory,
        letI := hSums
        ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          (constantModelBoundedConstructible Λ X K.obj ∧
            DerivedCategory.finiteTorAmplitude _ K.obj) → IsCompactObject K
```

The criterion and helper use the explicit six-case coefficient hypothesis of the
existing finite-field compactness theorem. They do not unfold the changed admissibility
predicate and require no new coefficient definition.

The proved private helper brownHypotheses_admissible_small specializes
 det_brown_hypotheses_small to all six actual admissibility alternatives on any compact
locally Noetherian scheme. Finite coefficient carriers use the existing explicit
finiteCoefficientLiftIso. Its construction is unchanged. Other cases use the zero
finite ring and bottom extension only as unused parameters, exactly as the old proof.
The new criterion applies this helper after the finite-type compact/Noetherian
instances and the existing formal Brown criterion. The finite-field specialization
uses the new criterion in its final assembly. Its signature and conclusion do not change.

Remove the obsolete warning about an additional all-continuous coefficient, since
that case is no longer in the source predicate. Keep the arbitrary-field warning and
its conditional counterexample discussion. No target meaning changes.

## Users

The source-only transitive downstream census has 393 modules. None uses the new
name beforehand. The three direct importers call the original brownHypotheses, whose
signature and proof hole remain unchanged. Every existing public signature and
public import is retained, so no adaptation or target-statement re-review is needed.
A held consumer is not edited. The table below records every transitive importer.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypotheses | R2 | New proved criterion; reuse in private finite-field proof. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerGeometricTransport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerSite | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ChartGeometricCounitEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedHomChainRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricOperations | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenCompactSupportExchange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenProperRestrictionIso | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestrictionMaps | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.P1CounitScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalAffineTensorCalculus | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1KernelContractions | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RelativeKunneth | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixCtf | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ScalarSixDirectImage | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| TargetsCheck | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.Statement | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Main | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Product | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not queried: no adaptation | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | Not queried: no adaptation | Existing interface unchanged; no adaptation. |

## Status

landed 20261025T071140-L-106437 2026-10-25 (merge of deliver/R2/Sheaf.SixFunctorsBasics.BrownHypotheses)
