# WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

## Reason

The delivery fills the five existing theorem holes. Server preflight requests a change
record because it detects additional instance, attribute, option, and section commands.
This record documents those proof-elaboration additions; it requests no change to an
existing declaration signature, attribute, public import, or non-theorem body.
All added declarations are proved private helpers. There are no new public declarations.
The item is held by F5; no other Lean module is edited.

The private continuity instances supply isomorphism, shift, and distinguished-extension
closure for the already defined canonical Hom-colimit property. The private module
instances cache existing tensor-colimit preservation and flat-resolution instances.
The private ambient functor instances supply shift compatibility and triangulation for
an auxiliary cocone used only in the object-descent proof. The imported finite-model
private instances are activated locally. Local instance priorities and irreducibility
keep elaboration of the unchanged source constructions within the existing time limit.
The `maxSynthPendingDepth` setting is restored before the new descent proofs; the
`maxHeartbeats` setting is confined to hom-surjectivity and changes no compile time limit.

## Old

No existing declaration or definition is replaced. The original header after the module
docstring is, verbatim:

```lean
@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The derived extensions of scalars and their transitivity -/
```

No declaration with any of these private names was present in the item:
`continuity_iso`, `continuity_shift`, `continuity_tri`, `moduleTensorColimits`,
`moduleTensorFlipColimits`, `moduleFlatResolution`, `ambientCommShift`,
`ambientTriangulated`. They are additions, not replacements for existing instances.

## New

The corresponding added commands and private instance declarations are reproduced
verbatim below. The original public header remains present; the temporary section
variables of HomContinuity end before the original namespace and variables resume.

```lean
attribute [local instance 20000]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape

set_option maxSynthPendingDepth 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian ZeroObject

open scoped CategoryTheory.Obj CategoryTheory.Functor

section HomContinuity

set_option linter.unusedSectionVars false
universe v w vI
open Opposite
namespace CategoryTheory
variable {D : Type w} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {I : Type v} [SmallCategory I] [IsFiltered I] (N : I ⥤ D) (c : Cocone N)
private instance continuity_iso : (homColimitProperty N c).IsClosedUnderIsomorphisms where
  of_iso e h n := desc_iso_transfer N c _ _
    (Functor.isoWhiskerLeft (shiftFunctor D n)
      (preadditiveCoyoneda.mapIso e.symm.op)) (h n)
private instance continuity_shift : (homColimitProperty N c).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K h ↦ homColimitProperty_shift N c K h n⟩
private instance continuity_tri : (homColimitProperty N c).IsTriangulated where
  exists_zero := by
    refine ⟨0, isZero_zero D, fun n ↦ ?_⟩
    have h (Y : D) : IsZero ((preadditiveCoyoneda.obj (op (0 : D))).obj Y) := by
      apply (IsZero.iff_id_eq_zero _).2
      ext f
      exact (isZero_zero D).eq_of_src _ _
    apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
    exact ⟨IsColimit.ofIsZero _ ((Functor.isZero_iff _).2 (fun i ↦ h _)) (h _)⟩
  toIsTriangulatedClosed₂ := .mk' (homColimitProperty_extensions N c)
end CategoryTheory
end HomContinuity

set_option linter.unusedSectionVars true
```

```lean
set_option maxSynthPendingDepth 3

attribute [local instance 100]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape



variable [TopologicalSpace.NoetherianSpace X]

attribute [local instance] moduleTensorFour moduleTensorLeft moduleTensorRight

private instance moduleTensorColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).obj M) :=
  fun _ ↦ inferInstance

private instance moduleTensorFlipColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      PreservesColimitsOfShape ℤ
        ((curriedTensor (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)).flip.obj M) :=
  fun _ ↦ inferInstance

private instance moduleFlatResolution {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by infer_instance

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
```

```lean
attribute [local instance] algClCommShift algClTriangulated

attribute [local instance 2000] finiteBoundedTriangulated
attribute [local irreducible] algClDerivedIso algClCommShift


attribute [local irreducible] derivedExtendScalarsCompIso
  finiteCoefficientDerivedTensorCompIso finiteCoefficientDerivedHomEquiv
  finiteCoefficientDerivedAlgClHomEquiv finiteCoefficientDerivedRestriction
  finiteCoefficientDerivedFromAlgCl finiteCoefficientDerivedAdjunction
  finiteCoefficientDerivedAlgClAdjunction

private noncomputable def ambientCocone :
    CategoryCocone (fun E : FiniteIntermediateField ℓ ↦ PadicSubfieldConstructible X ℓ E)
      (DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (padicAlgClRingObj X ℓ))) where
  T h := constructibleExtendScalars X ℓ h
  Φ E := (constructibleToPadicAlgCl X ℓ E) ⋙ (boundedConstructible (padicAlgClRingObj X ℓ)).ι
  iso h := (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constructibleToPadicAlgClCompIso X ℓ h) _
```

```lean
set_option backward.isDefEq.respectTransparency true in
private noncomputable instance ambientCommShift (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).ι
    (derivedExtendScalarsToPadicAlgCl X ℓ E) ℤ _ _ _ _
    (inferInstance) (algClCommShift X ℓ E)

set_option backward.isDefEq.respectTransparency true in
private instance ambientTriangulated (E : FiniteIntermediateField ℓ) :
    ((ambientCocone X ℓ).Φ E).IsTriangulated :=
  inferInstanceAs (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι ⋙
    derivedExtendScalarsToPadicAlgCl X ℓ E).IsTriangulated)


```

The declaration-scoped transparency and heartbeat settings on hom-surjectivity and
object descent, and the declaration-scoped unused-section-variable linter setting,
are proof-elaboration settings only. The actual source functors, tensor comparison,
constructible cocone, and two-colimit theorem retain their existing definitions and
signatures. The six original theorem signatures, three public imports, and nine
non-theorem bodies were compared textually with the source and are unchanged.

## Users

`tools/downstream.py` reports the following 228 transitive downstream modules.
The table records claim ownership when a claim file is present (otherwise unclaimed).
No consumer is adapted: the existing public interface is unchanged. The source archive
has similarly named private helpers of its own; the textual name matches reported by
`--uses` refer to those declarations, not to these newly private declarations.
The source archive and its Lean attachment and dependencies are preserved.
Target statements and all definitions occurring in them are unchanged, so this packet
introduces no target-meaning change requiring a renewed statement review.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | F5 (recorded claim) | Five existing holes proved; private proof support added. |
| `Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 (recorded claim) | Public interface unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentHom` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedBoundedHomContinuity` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedCompactSupportProjection` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClOpenScalarComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | K6 (recorded claim) | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizedHom` | C3 (recorded claim) | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CommonFieldLatticeGenerators` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FieldTensor` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | W4 (recorded claim) | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Public interface unchanged; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Public interface unchanged; no adaptation. |
| `TargetsCheck` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Public interface unchanged; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261021T225118-L-3772049 2026-10-21 (merge of deliver/F5/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit)
