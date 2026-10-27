/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

import all Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import all Sheaf.Paper.FiniteDiscreteEncodingCompactification
import all Sheaf.Paper.FiniteDiscreteEncodingConstructibility
import Sheaf.Paper.FiniteDiscreteEncodingTensorTor
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import all Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage
import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion
import Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Sheaf.Paper.ContinuousConstructibleIntegralModel
import Sheaf.Paper.ContinuousIntegralPushComparison
import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.Paper.QlbarDirectImageComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstructibleHeart
import Sheaf.AlgebraicGeometry.NativeAdicConstructibilityEncoding

/-!
# Adic finiteness for a dense open immersion with affine source

This is the open-immersion input for the affine compactification reduction of
`sk-prop-sf-finiteness`. It concerns ordinary direct image, including its boundary stalks.
-/

@[expose] public section

universe u

set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint ProEtale.CondensedRing.upperStar
  derivedPushHom derivedComapLowerStarIso Mod.derivedExtendMapDerivedCategoryAdjunction
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

private theorem open_finite_field_tor
    (F : Type (u + 1)) [Field F] (X : Scheme.{u})
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨hb, _⟩ := hK
  refine _root_.DerivedCategory.prop_of_bounded
    (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X) ⊤ ?_ K hb
    (fun _ ↦ trivial)
  intro G _
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance
private theorem open_finiteFixed_bounded
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (A : Type u) [Field A] [Finite A]
    (hA : (l : A) = 0)
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
  have hk : IsUnit (l : k) :=
    (CharP.cast_ne_zero_of_ne_of_prime k (p := ringChar k)
      (Fact.out : l.Prime) (Fact.out : ringChar k ≠ l)).isUnit
  have hcoeff : Etale.IsSmoothBaseChangeCoefficients l B (Spec (.of k)) :=
    ⟨(Fact.out : l.Prime).pos, inferInstance, by exact congrArg ULift.up hA,
      by simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  have hFJ := Etale.isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    k B l hcoeff t p J hJ
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
      open_finite_field_tor B Y hbc
    exact ⟨r, s, (_root_.DerivedCategory.torAmplitudeIn _ r s).prop_of_iso e
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff r s _).2 ht)⟩
private theorem open_finiteInternal_bounded
    (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (A : Type u) [Field A] [Finite A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    (hA : (l : A) = 0)
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
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let e : (E Y).fixedDerived.functor.obj
      (R((p)_*⟦ProEtale.FiniteDiscreteOrdinary.coefficient A⟧).obj K) ≅
      (ProEtale.lowerStar B p).rightDerivedFunctor.obj ((E Z).fixedDerived.functor.obj K) :=
    (ProEtale.FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A p (E Y) (E Z)).app K
  have hsource := (ProEtale.FiniteDiscreteOrdinary.encoding_constructibility A Z (E Z)).2 K
  have himage := open_finiteFixed_bounded l t p A hA _ (hsource.mp hK)
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
private theorem open_integralModel_bounded
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
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
  have hfinite := open_finiteInternal_bounded l t p A
    (ProEtale.IntegralOpenDirectImage.residue_killed l E)
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
private theorem open_integral_of_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (e : Mon.mk Λ ≅ Mon.mk (ProEtale.DerivedNakayama.integerRing l E))
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : boundedConstructible (condensedRingObj Λ Z) K) :
    boundedConstructible (condensedRingObj Λ Y) (R((p)_*⟦Λ⟧).obj K) := by
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
  have hP := open_integralModel_bounded l E t p _ hFK
  let hi : (F Y).mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K) ≅
      R((p)_*⟦ProEtale.DerivedNakayama.integerRing l E⟧).obj
        ((F Z).mapDerivedCategory.obj K) := (derivedComapLowerStarIso φ p).app K
  refine ⟨(F Y).bounded_of_bounded_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.bounded).prop_of_iso hi.symm hP.1), ?_⟩
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
private theorem open_continuous_of_integral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (hint : ∀ M : integralConstructible ℓ E Z,
      boundedConstructible (condensedRingObj (integralCoeff ℓ E) Y)
        (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K) := by
  -- Cache the module tensor structures used by the scalar-change adjunction.
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E Z ⟨K, hK⟩
  have := integralScalarPushHom_isIso ℓ E p M
  let φ := coefficientMap (integralScalarMap ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦integralCoeff ℓ E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj K :=
    asIso ((derivedPushHom (integralScalarMap ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧)).mapIso e
  have hs := ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ φ _ (hint M)
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e' hs.1,
    fun q ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e') (hs.2 q)⟩
private theorem open_qbar_of_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (t : Y ⟶ Spec (.of k)) [LocallyOfFiniteType t] [QuasiCompact t]
    (p : Z ⟶ Y) [IsOpenImmersion p] [QuasiCompact p]
    (hfinite : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (M : PadicSubfieldConstructible Z ℓ E),
      boundedConstructible (padicSubfieldRingObj Y ℓ E)
        (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicAlgClRingObj Z ℓ)))
    (hK : boundedConstructible (padicAlgClRingObj Z ℓ) K) :
    boundedConstructible (padicAlgClRingObj Y ℓ)
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) := by
  obtain ⟨E, M, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ ⟨K, hK⟩
  obtain ⟨N, hN⟩ := M.property.1.1
  have : M.obj.IsGE N := hN
  have := isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ E p ⟨M.obj, ⟨N, hN⟩⟩
  let e₀ := (boundedConstructible (padicAlgClRingObj Z ℓ)).ι.mapIso e
  let φ := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Y
  let e' : (Mod.extendScalars φ).leftDerivedFunctor.obj
      (R((p)_*⟦Profinite.continuousMapRingObj E⟧).obj M.obj) ≅
      R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K :=
    asIso ((derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p).app M.obj) ≪≫
      (R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso e₀
  have hs := ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _ φ _ (hfinite E M)
  exact ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e' hs.1,
    fun q ↦ _root_.constructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e') (hs.2 q)⟩
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- A constructible adic sheaf on a dense affine open has bounded constructible direct image.

Source: SGA 4½, *Théorème de finitude*, Theorem 1.1 and the open-immersion paragraph of
`sk-prop-sf-finiteness`; Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2,
Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-dense-open-direct-image-finiteness)

Proof: the finite-type target is noetherian and quasi-excellent, and ℓ is invertible on it.
On this target and its open subscheme, local constructibility is equivalent to a finite
lisse stratification. By Proposition 6.8.14, the sheaf in degree zero descends to a bounded
constructible complex over a finite extension E of Q_ℓ and is the rationalization of an
integral constructible complex C over O_E. This passage does not require a global lisse
lattice: Lemma 6.8.13 supplies constructible integral structures and the proof of
Proposition 6.8.14 glues them by the localization of extension groups.

For each power of a uniformizer of O_E, the reduction of C has finite torsion coefficients.
The open-immersion finiteness theorem makes its derived direct image constructible.
The torsion direct-image functor has a finite cohomological-dimension bound independent
of that power (Theorem 6.7.1); together with the two-term resolution of each coefficient
quotient, this gives a uniform finite interval for all the derived direct images of the
reductions. The complete direct image of C is derived complete, and reduction commutes
with direct image, by Lemmas 6.5.9 and 6.5.11. Lemma 6.7.2 consequently makes this integral
direct image constructible. Proposition 6.8.11 identifies this with boundedness and
constructible cohomology. Rationalization and passage to Q̄_ℓ carry this computation to
the ambient derived direct image of modules over the adic coefficient sheaf, as in
Remark 6.8.15. Thus the displayed right derived functor is bounded and all of its
cohomology sheaves are constructible. No bound by the dimensions of the fibres of the
open immersion is asserted. -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion
    (hK : ringChar K ≠ l) {Z W : Scheme.{u}} [IsAffine Z]
    (t : W ⟶ Spec (.of K)) [LocallyOfFiniteType t] [QuasiCompact t]
    (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j.base)
    (F : AdicSheaf l Z) (hF : IsAdicConstructibleSheaf F) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l W))
      ((j)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  have _ : IsAlgClosed K := inferInstance
  have _ := hj
  have : Fact (ringChar K ≠ l) := ⟨hK⟩
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian W := isNoetherian_of_locallyOfFiniteType t
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  let A := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let p := j
  have hA := (DerivedCategory.adicConstructibleHeart_singleFunctor_obj hF).1.1
  have hX := NativeEncoding.encoding_exact_derived l Z
  have hY := NativeEncoding.encoding_exact_derived l W
  let := hX.1
  let := hX.2.1
  let := hY.1
  let := hY.2.1
  have hencoded : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) Z)
      ((NativeEncoding.derivedEncoding l Z).obj A) := by
    refine ⟨(NativeEncoding.encoding l _).bounded_mapDerivedCategory_obj hA.1, ?_⟩
    intro q
    exact _root_.constructible_of_iso
      (((NativeEncoding.encoding l _).mapDerivedCategoryHomologyFunctorIso q).app A)
      ((encoding_constructible_iff _).mp (hA.2 q))
  have hint (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (M : CondensedRing.integralConstructible l E Z) :
      boundedConstructible (condensedRingObj (CondensedRing.integralCoeff l E) W)
        ((CondensedRing.lowerStar (CondensedRing.integralCoeff l E) p).rightDerivedFunctor.obj
          M.obj) := by
    let : FiniteDimensional ℚ_[l] (ULift.{u} E) :=
      (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
    exact CondensedRing.open_integral_of_iso l (ULift.{u} E) _
      (CondensedRing.integerNormedIso l E) t p M.obj M.property
  have hp := CondensedRing.open_qbar_of_finite l t p
    (fun E M ↦ CondensedRing.open_continuous_of_integral l E t p
      (hint E) M.obj M.property) _ hencoded
  have himage : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) W)
      ((NativeEncoding.derivedEncoding l W).obj ((adicLowerStar l p).rightDerivedFunctor.obj A)) :=
    ⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso
      ((NativeEncoding.derivedPushComparison l p).app A).symm hp.1,
      fun q ↦ _root_.constructible_of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
          ((NativeEncoding.derivedPushComparison l p).app A).symm) (hp.2 q)⟩
  refine ⟨(NativeEncoding.encoding l W).bounded_of_bounded_mapDerivedCategory_obj himage.1,
    fun q ↦ ?_⟩
  apply (encoding_constructible_iff _).mpr
  exact _root_.constructible_of_iso
    (((NativeEncoding.encoding l W).mapDerivedCategoryHomologyFunctorIso q).app
      ((adicLowerStar l p).rightDerivedFunctor.obj A)).symm (himage.2 q)

end AlgebraicGeometry.ProEtale
