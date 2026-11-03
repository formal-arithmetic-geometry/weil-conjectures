/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PodCondensedAutomorphismCompactExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SmoothPurity.WeilVerdierModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.CategoryTheory.NormalizedClosedExchange.NormalizedClosedAdjunctionExchange
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.Adjunction.CondensedSixOperationPreservation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFiniteAffineDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionBoundedDescent
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchangeIso
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.UnboundedBaseChangeExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.BrownRepresentabilityRightAdjoint
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! Ordinary pullback and direct-image lifts in blueprint proof step 1.
Source: prop-weil-operations (blueprint: lem-weil-operations-ordinary). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

set_option maxHeartbeats 1600000 in
-- Simultaneous ordinary unary-operation endpoints.
/-- The four carrier and ordinary-operation clauses of the original proposition.
Source: prop-weil-operations, step 1 (blueprint: lem-weil-operations-ordinary). -/
structure WeilOperationsOrdinary
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀))) (f₀ : X₀ ⟶ Y₀) (c : WeilCoefficient ell)
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left] : Prop where
  carrier_domain_X :
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left) =
      condensedConstructibleFiniteTor (WeilCoefficient.ab c) (D.geometricFiber X₀).left
  carrier_domain_Y :
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left) =
      condensedConstructibleFiniteTor (WeilCoefficient.ab c) (D.geometricFiber Y₀).left
  pullback :
    WOUnary
      (boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left))
      (boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left))
      (upperStar (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).mapDerivedCategory
      (upperStar (WeilCoefficient.ab c) (D.geometricFrobenius X₀).hom).mapDerivedCategory
      (moduleObjectDerivedPullback (WeilCoefficient.ab c) ((geometricFiberMap D f₀).left))
      (woPullExchange (WeilCoefficient.ab c) ((geometricFiberMap D f₀).left)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        ⟨(D.frobenius_square_cartesian _ _ f₀).2.2.2.2.1⟩)
  directImage :
    WOUnary
      (boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber X₀).left))
      (boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left))
      (upperStar (WeilCoefficient.ab c) (D.geometricFrobenius X₀).hom).mapDerivedCategory
      (upperStar (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).mapDerivedCategory
      (moduleObjectDerivedPushforward (WeilCoefficient.ab c) ((geometricFiberMap D f₀).left))
      (woPushExchange (WeilCoefficient.ab c) ((geometricFiberMap D f₀).left)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        ⟨(D.frobenius_square_cartesian _ _ f₀).2.2.2.2.1⟩)

private theorem woUnary_of_preserves
    {C : Type uC} [Category.{vC} C] {B : Type uD} [Category.{vD} B]
    (p : ObjectProperty C) (q : ObjectProperty B) (P : C ⥤ C) (Q : B ⥤ B)
    (F : C ⥤ B) (ex : F ⋙ Q ⟶ P ⋙ F) [IsIso ex]
    (hF : ∀ K : C, p K → q (F.obj K)) : WOUnary p q P Q F ex := by
  let L₀ := (ObjectProperty.ι (fun K : Endofunctor.IsoAlgebra P ↦ p K.carrier)) ⋙
    Endofunctor.IsoAlgebra.mapOfNatIso (asIso ex)
  let L := ObjectProperty.lift (fun K : Endofunctor.IsoAlgebra Q ↦ q K.carrier) L₀
    (fun K ↦ hF K.obj.carrier K.property)
  refine ⟨hF, inferInstance, L, Iso.refl _, ?_⟩
  intro K
  change Q.map (𝟙 _) ≫ (ex.app K.obj.carrier ≫ F.map K.obj.str.hom) =
    (ex.app K.obj.carrier ≫ F.map K.obj.str.hom) ≫ 𝟙 _
  simp

private theorem pullIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) : IsIso (woPullExchange Λ f gX gY sq) := by
  dsimp [woPullExchange]
  infer_instance

private theorem pushIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) : IsIso (woPushExchange Λ f gX gY sq) := by
  have := (condensed_isomorphism_square_exchange ⟨Λ⟩ sq).2.2.2.2.2.2
  dsimp [woPushExchange, FrobeniusSquareExchange.direct]
  infer_instance

private theorem woOverPullbackSquare
    {S T : Scheme.{u}} (f : T ⟶ S) {X Y : Over S} (g : X ⟶ Y) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst X.hom f)
      (pullback.fst Y.hom f) g.left := by
  have h : IsPullback (pullback.snd X.hom f) (pullback.fst X.hom f)
      f (g.left ≫ Y.hom) := by
    simpa only [Over.w] using (IsPullback.of_hasPullback X.hom f).flip
  have hout : IsPullback
      (((Over.pullback f).map g).left ≫ pullback.snd Y.hom f)
      (pullback.fst X.hom f) f (g.left ≫ Y.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd] using h
  exact hout.of_right (by simp) (IsPullback.of_hasPullback Y.hom f).flip

set_option maxHeartbeats 1600000 in
-- The ordinary operation block is isolated from compact and comparison constructions.
/-- Carrier equalities and the normalized pullback/direct-image lifts.
Source: prop-weil-operations.proof.md, first two sentences
(blueprint: lem-weil-operations-ordinary).

Proof: introduce characteristic and finite-field instances from the cardinality of the
base field, then apply condensed six-operation preservation at the finite or algebraically
closed coefficient. Its finite-Tor equality yields the carrier identities. Restrict the
actual derived adjunction to bounded constructibles and transport the specified
Frobenius-square exchanges through exact/derived comparisons. `mapOfNatIso` gives the
fixed-pair lifts with identity carrier comparisons; naturality gives the arrow laws.
The geometric base-change square supplies separatedness for the pullback map. -/
theorem weilOperations_ordinary
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    (f₀ : X₀ ⟶ Y₀) (c : WeilCoefficient ell)
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left] :
    WeilOperationsOrdinary D ell hEll X₀ Y₀ f₀ c := by
  classical
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨by rw [ringChar.eq D.k D.p]; exact hEll.symm⟩
  let E : PadicAlgCl.FiniteIntermediateField ell := match c with
    | .finite E => E
    | .qbar => ⟨⊥, inferInstance⟩
  have hΛ : Nonempty (Mon.mk (WeilCoefficient.ab.{u} c) ≅
      Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk (WeilCoefficient.ab.{u} c) ≅
        Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    cases c with
    | finite E => exact Or.inl ⟨Iso.refl _⟩
    | qbar => exact Or.inr ⟨Iso.refl _⟩
  have h := condensedSixOperationPreservation_finite_or_algClosed ell D.k
    (Or.inr inferInstance) E (WeilCoefficient.ab.{u} c) hΛ
  have hX := (h.1 (D.geometricFiber X₀)).1
  have hY := (h.1 (D.geometricFiber Y₀)).1
  let f := geometricFiberMap D f₀
  have : LocallyOfFiniteType (f.left ≫ (D.geometricFiber Y₀).hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left :=
    locallyOfFiniteType_of_comp f.left (D.geometricFiber Y₀).hom
  have : IsNoetherian (D.geometricFiber X₀).left :=
    isNoetherian_of_locallyOfFiniteType (D.geometricFiber X₀).hom
  have : IsSeparated f.left := by
    exact MorphismProperty.of_isPullback
      (woOverPullbackSquare
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀).flip inferInstance
  obtain ⟨hF, hG, _⟩ := (h.2 (D.geometricFiber X₀) (D.geometricFiber Y₀)
    (geometricFiberMap D f₀)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext K
    constructor
    · intro hK
      have hh : (constantModelBoundedConstructible (WeilCoefficient.ab c)
          (D.geometricFiber X₀).left ⊓ fun M ↦ DerivedCategory.finiteTorAmplitude _ M) K := by
        rw [← hX]
        exact hK
      exact ⟨hK, hh.2⟩
    · exact fun hK ↦ hK.1
  · ext K
    constructor
    · intro hK
      have hh : (constantModelBoundedConstructible (WeilCoefficient.ab c)
          (D.geometricFiber Y₀).left ⊓ fun M ↦ DerivedCategory.finiteTorAmplitude _ M) K := by
        rw [← hY]
        exact hK
      exact ⟨hK, hh.2⟩
    · exact fun hK ↦ hK.1
  · let := pullIso (WeilCoefficient.ab c) (geometricFiberMap D f₀).left
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      ⟨(D.frobenius_square_cartesian _ _ f₀).2.2.2.2.1⟩
    exact woUnary_of_preserves _ _ _ _ _ _ (fun K hK ↦ hF ⟨K, hK⟩)
  · let := pushIso (WeilCoefficient.ab c) (geometricFiberMap D f₀).left
      (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
      ⟨(D.frobenius_square_cartesian _ _ f₀).2.2.2.2.1⟩
    exact woUnary_of_preserves _ _ _ _ _ _ (fun K hK ↦ hG ⟨K, hK⟩)

end WeilConjectures
