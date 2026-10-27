/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import all Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion
import Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits
import all Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.Paper.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import all Sheaf.AlgebraicGeometry.FiniteProperClassicalCoproducts
import all Sheaf.Paper.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.FiniteDiscreteEncodingCompactification
import all Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import Sheaf.Paper.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import Sheaf.Paper.ContinuousConstructibleIntegralModel
import Sheaf.Paper.ContinuousIntegralPushComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Constructibility of proper ell-adic direct-image cohomology

This is the constructibility assertion of proper finiteness, separated from the
uniform cohomological-dimension estimate.
(blueprint: lem-sfb-noetherian-proper-constructible-cohomology)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj
  Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived


variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open _root_.DerivedCategory CategoryTheory.Pretriangulated in
private lemma proper_bounded_induction (P : ObjectProperty (_root_.DerivedCategory C))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (h : ∀ G : C, P ((singleFunctor C 0).obj G)) (K : _root_.DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] : P K := by
  exact prop_of_bounded P ⊤ (fun G _ ↦ h G) K
    ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩ (fun _ ↦ trivial)


private theorem proper_finite_field_tor
    (F : Type (u + 1)) [Field F] (X : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, -⟩ := hK
  refine proper_bounded_induction _ (fun G ↦ ?_) K a b
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance


/-- The finite-coefficient input to the integral argument. Properness allows the
compactification with identity open immersion, so the compact-support finiteness
statement is exactly ordinary direct-image constructibility. -/
private theorem proper_finiteEtale_constructible
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∀ (a : A) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj K.obj)) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K.obj)) := by
  let c := Compactification.ofIsProper p
  have h := Etale.isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate
    A hA p c K hK q
  let e : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor :=
    Functor.isoWhiskerRight
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) Z)
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor ≪≫
        Functor.leftUnitor _
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj)) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact Scheme.IsConstructibleSheaf.of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso (e.app K.obj))

private theorem proper_finiteEtale_bounded
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∀ (a : A) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (K : Etale.DerivedCategoryModule A Z)
    (hK : Etale.DerivedCategory.isBoundedConstructible A Z K) :
    Etale.DerivedCategory.isBoundedConstructible A Y
      ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K) := by
  obtain ⟨a, b, hab, hv⟩ := hK.2
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2 fun q hq ↦ hv q (Or.inl hq)
  have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun q hq ↦ hv q (Or.inr hq)
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  have hcd := ProEtale.etale_cd A p d hd
  have hge := Functor.isGE_rightDerivedFunctor_obj
    (Etale.lowerStar (ModuleCat.{u + 1} A) p) K a
  have hle := Functor.isLE_rightDerivedFunctor_obj
    (Etale.lowerStar (ModuleCat.{u + 1} A) p) (2 * d) hcd K b
  refine ⟨proper_finiteEtale_constructible p A hA ⟨K, ⟨a, inferInstance⟩⟩ hK.1,
    a, b + (2 * d : ℕ), by omega, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := hge)
  · exact DerivedCategory.isZero_of_isLE _ (b + (2 * d : ℕ)) q hq (hX := hle)

private theorem proper_finiteFixed_bounded
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (A : Type u) [Field A] [Finite A]
    (hA : ∀ (a : A) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Z K) :
    ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).rightDerivedFunctor.obj
          K) := by
  let B := ULift.{u + 1} A
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hK.1
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := ProEtale.fixedDerivedOrigin Z B K
    (fun q ↦ (ProEtale.ordinary_constructible_iff A Z _).mp (hK.2 q)) a b (by
      intro q hq
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := ha)
      · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := hb))
  have hB (b : B) (y : Y) : IsUnit (addOrderOf b : Y.presheaf.stalk y) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero
      (ULift.ext _ _ (addOrderOf_nsmul_eq_zero b.down)))) (hA b.down y)
  have hFJ := proper_finiteEtale_bounded p B hB J hJ
  obtain ⟨aJ, bJ, _, hvJ⟩ := hJ.2
  let Jp : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat B)) :=
    ⟨J, ⟨aJ, (DerivedCategory.isGE_iff J aJ).2
      (fun q hq ↦ hvJ q (Or.inl hq))⟩⟩
  let νY := ProEtale.comparisonUpperStar (ModuleCat B) Y
  let F := Etale.lowerStar (ModuleCat B) p
  let G := ProEtale.lowerStar (ModuleCat B) p
  let e : νY.mapDerivedCategory.obj (F.rightDerivedFunctor.obj J) ≅
      G.rightDerivedFunctor.obj K :=
    ((ProEtale.rightDerivedLowerStarComparisonIso (ModuleCat B) p).app Jp).symm ≪≫
      G.rightDerivedFunctor.mapIso eJ
  obtain ⟨c, d, _, hv⟩ := hFJ.2
  have hge : (F.rightDerivedFunctor.obj J).IsGE c :=
    (DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hv q (Or.inl hq)
  have hle : (F.rightDerivedFunctor.obj J).IsLE d :=
    (DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hv q (Or.inr hq)
  have := νY.isGE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) c
  have := νY.isLE_mapDerivedCategory_obj (F.rightDerivedFunctor.obj J) d
  constructor
  · refine ⟨⟨⟨c, DerivedCategory.TStructure.t.isGE_of_iso e c⟩,
      ⟨d, DerivedCategory.TStructure.t.isLE_of_iso e d⟩⟩, ?_⟩
    intro q
    apply (ProEtale.ordinary_constructible_iff A Y _).mpr
    have : Scheme.IsConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj (F.rightDerivedFunctor.obj J)) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)
    exact ProEtale.isConstructible_of_iso
      ((νY.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
      (ProEtale.isConstructible_comparisonUpperStar_obj _)
  · have hbc : Etale.DerivedCategory.boundedConstructible (ModuleCat B) Y
        (F.rightDerivedFunctor.obj J) := by
      refine ⟨⟨⟨c, hge⟩, ⟨d, hle⟩⟩, fun q ↦
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hFJ.1 q)⟩
    obtain ⟨r, s, ht⟩ :=
      proper_finite_field_tor B Y hbc
    exact ⟨r, s, (_root_.DerivedCategory.torAmplitudeIn _ r s).prop_of_iso e
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff r s _).2 ht)⟩

private theorem proper_finiteInternal_bounded
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (A : Type u) [Field A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (hA : ∀ (a : A) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y))
    (K : DerivedCategory (ProEtale.FiniteDiscreteOrdinary.Internal A Z))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.FiniteDiscreteOrdinary.coefficient A) Z K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.FiniteDiscreteOrdinary.coefficient A) Y
      (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) := by
  classical
  let E (T : Scheme.{u}) : ProEtale.FiniteDiscreteOrdinary.Encoding A T :=
    (ProEtale.FiniteDiscreteOrdinary.encoding_exists A T).some
  let c := Compactification.ofIsProper p
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let e₀ : rightDerivedLowerShriekOfCompactification
      (ProEtale.FiniteDiscreteOrdinary.coefficient A) c ≅
      R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧) :=
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (((openImmersionLowerShriekUpperStarAdjunction
            (ProEtale.FiniteDiscreteOrdinary.coefficient A) (𝟙 Z)).ofNatIsoRight
            (upperStarId (ProEtale.FiniteDiscreteOrdinary.coefficient A) Z)).leftAdjointUniq
            Adjunction.id) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
      Functor.leftUnitor _
  let e₁ : ProEtale.rightDerivedLowerShriekOfCompactification B c ≅
      (ProEtale.lowerStar B p).rightDerivedFunctor :=
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (ProEtale.openImmersionLowerShriekIdIso B Z) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _
  let e : (E Y).fixedDerived.functor.obj
      (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) ≅
      (ProEtale.lowerStar B p).rightDerivedFunctor.obj ((E Z).fixedDerived.functor.obj K) :=
    (E Y).fixedDerived.functor.mapIso (e₀.app K).symm ≪≫
      ((ProEtale.FiniteDiscreteOrdinary.encoding_compactification A E Z Y p c).some.app K) ≪≫
      e₁.app _
  have hsource := (ProEtale.FiniteDiscreteOrdinary.encoding_constructibility A Z (E Z)).2 K
  have himage := proper_finiteFixed_bounded p A hA _ (hsource.mp hK)
  have hb : ProEtale.FiniteDiscreteOrdinary.ordinaryBoundedConstructible A Y
      ((E Y).fixedDerived.functor.obj
        (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K)) := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm himage.1.1, ?_⟩
    intro q
    exact (ProEtale.FiniteDiscreteOrdinary.constructible_iso A Y
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)).mp (himage.1.2 q)
  refine ⟨(ProEtale.FiniteDiscreteOrdinary.encoding_constructibility A Y (E Y)).2 _ |>.mpr hb,
    ?_⟩
  obtain ⟨a, b, ht⟩ := himage.2
  have ht := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht
  exact ⟨min a b, b,
    ((ProEtale.FiniteDiscreteOrdinary.encoding_tensor_tor A Y (E Y)).2.2 _ _ _
      (min_le_right a b)).mpr (ht.mono (min_le_left a b) le_rfl)⟩

/-- The prime `l` vanishes in the residue field of the integers of a finite extension
of `ℚ_l`: its absolute value `1 / l` is below one, so it lies in the maximal ideal. -/
private theorem coefficientExtensionRing_one_natCast_self
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : Padic.coefficientExtensionRing l E 1) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hext : ∀ a : ℚ_[l],
      Padic.coefficientExtensionAbsoluteValue l E (algebraMap ℚ_[l] E a) = ‖a‖ :=
    spectralNorm_extends (K := ℚ_[l]) (L := E)
  have hmem : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    refine (h.2.1 _).2 ?_
    have hc : ((l : Padic.coefficientExtensionIntegers l E) : E) = algebraMap ℚ_[l] E l := by
      simp
    rw [hc, hext, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) l,
    Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal, pow_one, hg]
  exact hmem

private theorem proper_integralModel_bounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (ProEtale.AdicCompletion.Modules l E Z))
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Z K) :
    ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Y
      (R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E 1
  let : (Padic.coefficientExtensionIdeal l E 1).IsMaximal :=
    by
      have h := (Padic.extension_integers_dvr l E
        (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
      have hm : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
      have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
          Set (Padic.coefficientExtensionIntegers l E)) =
          Padic.coefficientExtensionMaximalIdeal l E :=
        h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
      simpa only [Padic.coefficientExtensionIdeal, pow_one, hg] using hm
  let : Field A := Ideal.Quotient.field _
  let : Finite A := Padic.finite_coefficientExtensionRing l E 1 le_rfl
  let : DiscreteTopology A := ProEtale.DerivedNakayama.quotientDiscrete l E 1
  have hsource := (ProEtale.internal_integral_residue_criterion l E Z).1 K |>.mp hK
  have hl0 : (l : A) = 0 := coefficientExtensionRing_one_natCast_self l E
  have hA (a : A) (y : Y) : IsUnit (addOrderOf a : Y.presheaf.stalk y) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (addOrderOf_dvd_of_nsmul_eq_zero
      (by rw [nsmul_eq_mul, hl0, zero_mul]))) (hl y)
  have hfinite := proper_finiteInternal_bounded p A hA
    ((ProEtale.AdicCompletion.derivedReduction l E Z 0).obj K) hsource.2.1
  have hlimits := ProEtale.internal_integral_direct_image_limits l E p
  have hχ := hlimits.choose
  have hpush := hlimits.choose_spec
  let := hχ
  have hcomplete := (hpush K).1 hsource.1
  have hiso := (hpush K).2
  let e : (ProEtale.AdicCompletion.derivedReduction l E Y 0).obj
      (R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj K) ≅
      R((p)_*⟦ProEtale.DerivedNakayama.quotientRing l E 1⟧).obj
        ((ProEtale.AdicCompletion.derivedReduction l E Z 0).obj K) :=
    @asIso _ _ _ _ _ hiso
  have hc := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing l E 1) Y).2.1
  have ht := (ProEtale.constantModelConstructibleFiniteTor_wellDefined
    (ProEtale.DerivedNakayama.quotientRing l E 1) Y).2.2.2.1
  let := hc
  let := ht
  exact (ProEtale.internal_integral_residue_criterion l E Y).1 _ |>.mpr
    ⟨hcomplete, (ProEtale.constantModelBoundedConstructible _ Y).prop_of_iso e.symm hfinite.1,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hfinite.2⟩

private noncomputable def continuousRingIso
    {A B : Type u} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

private noncomputable def continuousSmallRingIso
    {A : Type u} {B : Type} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

@[irreducible] private noncomputable def integerLatticeIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (ProEtale.integralCondensedRing l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := ProEtale.latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let e : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.val.ofAbs, x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ x.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact continuousRingIso e he.continuous he'.continuous

private theorem integerModel_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X)) :
    IsConstructibleModuleObject (condensedRingObj
      (ProEtale.DerivedNakayama.integerRing l E) X) M ↔
      ProEtale.IsConstantModelConstructible (ProEtale.DerivedNakayama.integerRing l E) X M :=
  ProEtale.comparison_transport (integerLatticeIso l E) X
    (ProEtale.integralLfpConstantModelComparison l E X) M

@[irreducible] private noncomputable def integerNormedIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCoeff.{u} l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l (ULift.{u} E)) := by
  let F := ULift.{u} E
  let : FiniteDimensional ℚ_[l] F :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  letI : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  letI : NormedAlgebra ℚ_[l] F := ⟨fun a x ↦ norm_smul_le a x.down⟩
  have hn (x : F) : spectralNorm ℚ_[l] F x = ‖x.down‖ :=
    (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (L := F) x).symm
  have hm (x : F) : x ∈ Padic.coefficientExtensionIntegers l F ↔
      x.down ∈ continuousIntegers l E := by
    have h := (Padic.extension_integers_dvr l F
      (Padic.coefficientExtensionAbsoluteValue l F)
      (spectralNorm_extends (K := ℚ_[l]) (L := F))).choose_spec.choose_spec.1 x
    change x ∈ Padic.coefficientExtensionIntegers l F ↔
      Padic.coefficientExtensionAbsoluteValue l F x ≤ 1 at h
    change _ ↔ ‖x.down‖₊ ≤ 1
    rw [h]
    change spectralNorm ℚ_[l] F x ≤ 1 ↔ _
    rw [hn]
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x.down‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x.down‖₊ ≤ 1)
  let A := ProEtale.latticeCoefficientIntegers l F
  let e : A ≃+* continuousIntegers l E :=
    { toFun := fun x ↦ ⟨x.val.ofAbs.down, (hm x.val.ofAbs).mp x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ (ULift.up x.val), (hm _).mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    change ‖x.val.ofAbs.down‖ = spectralNorm ℚ_[l] F x.val.ofAbs
    exact (hn x.val.ofAbs).symm
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact (continuousSmallRingIso e he.continuous he'.continuous).symm ≪≫
    integerLatticeIso l F


private theorem proper_integral_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (ProEtale.DerivedNakayama.integerRing l E))
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y)
      ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K)) := by
  let φ := e.inv.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F (X : Scheme.{u}) : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X) :=
    Mod.comap (coefficientMap φ X)
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ X)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  have hFK : ProEtale.constantModelBoundedConstructible
      (ProEtale.DerivedNakayama.integerRing l E) Z ((F Z).mapDerivedCategory.obj K) := by
    constructor
    · exact (F Z).bounded_mapDerivedCategory_obj hK.1
    intro q
    apply (integerModel_comparison l E Z _).mp
    exact _root_.constructible_of_iso
      (((F Z).mapDerivedCategoryHomologyFunctorIso q).app K)
      (_root_.constructible_comap (coefficientMap φ Z) (hK.2 q))
  have hP := proper_integralModel_bounded l E p hl _ hFK
  let hi : (F Y).mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K) ≅
      R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj
        ((F Z).mapDerivedCategory.obj K) := (derivedComapLowerStarIso φ p).app K
  intro q
  have hH := (integerModel_comparison l E Y _).mpr (hP.2 q)
  have hF : IsConstructibleModuleObject
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) Y)
      ((F Y).obj ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K))) :=
    _root_.constructible_of_iso
      (((DerivedCategory.homologyFunctor _ q).mapIso hi).symm ≪≫
        ((F Y).mapDerivedCategoryHomologyFunctorIso q).symm.app _) hH
  let ψ := coefficientMap φ Y
  exact _root_.constructible_of_iso
    (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app _)
    (_root_.constructible_comap (inv ψ) hF)

/-- A prime different from the characteristic of `k` is a unit in every stalk of a
scheme over `k`. -/
private theorem isUnit_natCast_stalk_of_ringChar_ne
    {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] (hk : ringChar k ≠ l)
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) (y : Y) :
    IsUnit (l : Y.presheaf.stalk y) := by
  have hl : (l : k) ≠ 0 := by
    intro h
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).1 (ringChar.dvd h) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hk h1
  have h1 : IsUnit (l : (Spec (.of k)).presheaf.stalk (aY y)) := by
    simpa using (isUnit_iff_ne_zero.2 hl).map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (aY y) trivial).hom
  simpa using h1.map (aY.stalkMap y).hom

private theorem constructible_derived_extend
    (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S))
    (e : (Mod.extendScalars φ).leftDerivedFunctor.obj K ≅ L)
    (q : ℤ) (h : IsConstructibleModuleObject R
      ((DerivedCategory.homologyFunctor _ q).obj K)) :
    IsConstructibleModuleObject S ((DerivedCategory.homologyFunctor _ q).obj L) := by
  have h' := ProEtale.constructible_extend R S φ h
  have h'' := _root_.constructible_of_iso
    (((Mod.extendScalars φ).leftDerivedFunctorHomologyFunctorIso q).app K) h'
  exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e) h''

private theorem proper_continuous_of_integral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y)
    [IsProper p]
    (hint : ∀ M : integralConstructible ℓ E Z, ∀ q : ℤ,
      IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    ∀ q : ℤ, IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K)) := by
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E Z ⟨K, hK⟩
  have := integralScalarPushHom_isIso ℓ E p M
  let φ := coefficientMap (integralScalarMap ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K :=
    asIso ((derivedPushHom (integralScalarMap ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧)).mapIso e
  intro q
  exact constructible_derived_extend Y _ _ φ _ _ e' q (hint M q)

private theorem proper_qbar_of_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y)
    [IsProper p]
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (M : PadicSubfieldConstructible Z ℓ E), ∀ q : ℤ,
      IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj)))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicAlgClRingObj Z ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj Z ℓ) K) :
    ∀ q : ℤ, IsConstructibleModuleObject (padicAlgClRingObj Y ℓ)
      ((DerivedCategory.homologyFunctor _ q).obj
        (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K)) := by
  obtain ⟨E, M, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ ⟨K, hK⟩
  obtain ⟨N, hN⟩ := M.property.1.1
  have : M.obj.IsGE N := hN
  have := isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE ℓ p E M.obj N
  let e₀ := (boundedConstructible (padicAlgClRingObj Z ℓ)).ι.mapIso e
  let φ := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K :=
    asIso ((derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e₀
  intro q
  exact constructible_derived_extend Y _ _ φ _ _ e' q (hfinite E M q)

/-- Every cohomology module of the proper direct image of a bounded constructible
ell-adic complex is constructible, over a Noetherian base.

Source: Bhatt--Scholze, Theorem 6.7.1, Lemma 6.7.2 and Remark 6.8.15;
blueprint sk-thm-sfb-proper-base-change,
integral and rational proper finiteness, constructibility clauses.
(blueprint: lem-sfb-noetherian-proper-constructible-cohomology)

Proof: first place a constructible module in degree zero. For integral coefficients,
its derived reductions modulo powers of a uniformizer are constructible torsion
complexes. Proper torsion finiteness makes their higher direct images constructible;
proper base change identifies the reductions and their transition maps. Derived
completeness and the compatible finite presentations on a common finite stratification
recover finitely presented integral local models for each cohomology sheaf. For finite
rational coefficients choose integral lattices on the strata. Proper pushforward
commutes with inverting ell by bounded-below qcqs continuity. The integral result,
localization and extension by zero therefore give constructibility. For condensed
Qlbar the finitely many local models descend to a common finite coefficient field;
finite coefficient extension and bounded-below continuity identify the scalar-extended
proper images. This proves the assertion for a constructible heart object. The
constructible modules over each of these coefficient rings are closed under kernels,
cokernels and extensions on a Noetherian scheme. Induction on the finite cohomological
interval of K, using its good-truncation triangles, then proves the same assertion
for K: in every degree the middle cohomology of the image triangle is an extension
of a cokernel by a kernel of constructibles. All steps are local on the target and
use proper finiteness over a Noetherian base, without a finite-type structure map to k.
The zero complex and empty strata are included.
-/
theorem properLowerStar_constructible_cohomology_ellAdic
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsEllAdicFinitenessCoefficient ℓ Λ]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Y)
      ((DerivedCategory.homologyFunctor _ q).obj (R((p)_*⟦Λ⟧).obj K)) := by
  classical
  have hl (y : Y) : IsUnit (ℓ : Y.presheaf.stalk y) :=
    isUnit_natCast_stalk_of_ringChar_ne ℓ Fact.out aY y
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  have hint (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] (M : integralConstructible ℓ E Z) :
      ∀ q : ℤ, IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y)
        ((DerivedCategory.homologyFunctor _ q).obj
          (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj)) := by
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
    exact proper_integral_of_iso ℓ (ULift.{u} E) _ (integerNormedIso ℓ E)
      p hl M.obj M.property
  cases (inferInstance : IsEllAdicFinitenessCoefficient ℓ Λ) with
  | continuous E =>
    exact proper_continuous_of_integral ℓ E p (hint E) K hK
  | integral E =>
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
    obtain ⟨e⟩ := ProEtale.integralCoefficientIso.{u} ℓ E
    exact proper_integral_of_iso ℓ (ULift.{u} E) _
      (e.symm ≪≫ integerLatticeIso ℓ (ULift.{u} E)) p hl K hK
  | algebraicClosure =>
    exact proper_qbar_of_finite ℓ p
      (fun E M ↦ proper_continuous_of_integral ℓ E p (hint E) M.obj M.property) K hK
  | unitBall E O hO =>
    have h : O = continuousIntegers ℓ E := by
      ext x
      rw [hO]
      change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
      simpa only [NNReal.coe_one, coe_nnnorm] using
        (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
    subst O
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
    exact proper_integral_of_iso ℓ (ULift.{u} E) _ (integerNormedIso ℓ E) p hl K hK

end AlgebraicGeometry.ProEtale.CondensedRing
