# AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_sheaves

## Reason

Restore the assigned quarantined module from coord/rework.tsv. The archive was removed
by the merge queue after a cluster restore, rather than withdrawn mathematically.
Its complete proof compiles against the current library. Simplify the open-counit
proof by lifting abelian direct-image full faithfulness, removing the private helper
openUnitIsIso and its direct module-lower-shriek proof import. The replacement private
import is the abelian open-restriction module. No public declaration, definition body,
public import, instance, or attribute is changed relative to the archive. No target
statement review is reopened.

## Old

The live item source is absent. The preserved quarantine source has these public
signatures (section parameters Λ, MonObj Λ, IsCommMonObj Λ are unchanged):

```lean
noncomputable def moduleSectionsWithSupport {X V : Scheme.{u}} (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ X

noncomputable def closedModuleSectionsWithSupport {X Z V : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ Z

theorem formal_closed_support_sheaves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    IsIso (Functor.whiskerLeft (moduleSectionsWithSupport Λ j)
      (upperStarLowerStarAdjunction Λ i).unit) ∧
    PreservesFiniteLimits (lowerStar Λ i) ∧
    PreservesFiniteColimits (lowerStar Λ i) ∧
    Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j) ∧
    PreservesFiniteLimits (closedModuleSectionsWithSupport Λ i j) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (closedModuleSectionsWithSupport Λ i j) ∧
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      (∀ I : CochainComplex (pulledBackModuleObjects Λ X) ℤ,
        I.IsKInjective →
          CochainComplex.IsKInjective
            (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ I : pulledBackModuleObjects Λ X, Injective I →
        Injective ((closedModuleSectionsWithSupport Λ i j).obj I))
```

## New

The same public signatures, byte for byte, are restored at the original module path.
Both definition bodies and every public import are byte-identical to the archive.
Only the private proof route for the open counit is shortened. The support kernel,
its canonical closed unit, and the adjunction target remain the specified constructions.

## Users

The stock downstream.py query reports unknown module because the live source is
quarantined. The table conservatively computes the transitive import closure using
both live and quarantined sources, preferring live sources where both exist.
Direct importers are FormalClosedSupportDerived (public import) and
IntegralRestrictionLine (private proof import). All listed users keep exactly their
archived API; none is edited or requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Restored API identical to archive; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | D3 | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Restored API identical to archive; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Restored API identical to archive; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Restored API identical to archive; no adaptation. |

## Status

landed 20261021T014701-L-2443828 2026-10-21 (merge of deliver/D3/Sheaf.Paper.FormalClosedSupportSheaves)
