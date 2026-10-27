# constant_square_zero_tor_example private proof context

## Reason

Server preflight classifies the added universe, namespace, variable, open and option
commands as a possible interface change. They support fully proved private helpers
for the internal periodic resolution and the finite-free two-term complex. Every
existing public signature and public import stays identical. There are no existing
non-theorem definitions in this module to change, and no consumer adaptation is needed.
No target statement or definition used by a target changes meaning.

## Old

The original commands after the public-section marker were:

```lean
set_option autoImplicit false
open CategoryTheory Limits
open scoped CategoryTheory.Obj MonoidalCategory
namespace AlgebraicGeometry.ProEtale
```

The original public declaration signature is preserved verbatim:

```lean
theorem constant_square_zero_tor_example (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅
      Mon.mk (Profinite.continuousCoefficientRingObj.{0} (ZMod (ℓ ^ 2)))))
    (k : Type) [Field k] [IsSepClosed k] :
    let X : Scheme.{0} := Scheme.Spec.obj (Opposite.op (CommRingCat.of k))
    let C := Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ
    let P := cokernel ((ℓ : ℕ) • (𝟙 (𝟙_ C)))
    let Cₓ := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
    let M : Cₓ := ((upperStarFromPoint X).mapMod Λ).obj P
    IsConstantModelConstructible Λ X M ∧
    ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
      ((_root_.DerivedCategory.singleFunctor Cₓ 0).obj M) ∧
    ∃ K : DerivedCategory Cₓ,
      (constantModelBoundedConstructible Λ X ⊓
        _root_.DerivedCategory.finiteTorAmplitude Cₓ) K ∧
      ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
        ((_root_.DerivedCategory.TStructure.t.truncGE 0).obj K)
```

## New

The proof context before the first private helper is now:

```lean
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits
open scoped CategoryTheory.Obj MonoidalCategory ZeroObject
open MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.SquareZeroInternal

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{w} C]
```

The generic variables are confined to the namespace
`CategoryTheory.SquareZeroInternal`, which ends before the existing namespace
`AlgebraicGeometry.ProEtale` opens. The added definitions and theorems are all private
and fully proved; no instance or attribute is exported. Local instances introduced
inside individual proofs provide exactness, additivity, or nonemptiness only there.
The statement's existing public-section marker and three public imports remain.
The other imports provide proof dependencies only. The public declaration has exactly
the signature quoted under Old, with its proof replacing the original `sorry`.

## Users

`tools/downstream.py Sheaf.Paper.ConstantSquareZeroTorExample
--uses constant_square_zero_tor_example` found the modules below. The only direct
importer and external textual consumer is `Sheaf.Paper.LocalizingClosureCtfEqualsBc`,
whose three applications at the Examples clauses were read: they use precisely the
same constructibility, infinite-amplitude and truncation conclusions. All consumer
statements therefore retain their meanings, with no forced adaptations. Holders below
are those recorded in `coord/claims` at preparation time; unclaimed means no record.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantSquareZeroTorExample | E3 | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | F6 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | X2 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | D7 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | Q3 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | Q4 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | C4 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | D3 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | M8 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | D4 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | J6 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | M6 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | P1 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.P1CounitScalar | U3 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | V1 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | W4 | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | E4 | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | M8 | Public signature and data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public signature and data unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signature and data unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public signature and data unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signature and data unchanged; no adaptation. |

## Status

landed 20261022T202019-L-1249487 2026-10-22 (merge of deliver/E3/Sheaf.Paper.ConstantSquareZeroTorExample)
