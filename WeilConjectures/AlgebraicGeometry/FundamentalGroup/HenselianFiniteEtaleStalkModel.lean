/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HenselianBoundaryLocalData
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField

import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.RingTheory.IntegralClosureIndEtaleBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Extension
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull
import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.TraceFormula.HenselizationPrimeIndEtale
import WeilConjectures.RingTheory.GeneralizedHenselizationAtPrime
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain

/-!
# Descent of a henselian generic model to the boundary stalk

Source: Stacks Project, Tags 0BSM, 0CBF, 02LA and 02VN.
(blueprint: lem-dl-a1-henselian-finite-etale-stalk-model).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

private theorem normal_generic_normalization_iso
    (C : Scheme.{u}) [IsIntegral C]
    (hnormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) :
    IsIso C.fromSpecFunctionField.fromNormalization := by
  have h := C.isIso_fromNormalization_restrict ⊤ (fun x _ ↦ hnormal x)
  have : IsIso (⊤ : C.Opens).ι := C.topIso.isIso_hom
  have : IsIso (C.fromNormalization ⁻¹ᵁ ⊤).ι := by
    simpa using C.normalization.topIso.isIso_hom
  have : IsIso ((C.fromNormalization ∣_ ⊤) ≫ (⊤ : C.Opens).ι) := inferInstance
  rw [morphismRestrict_ι] at this
  exact (isIso_comp_left_iff _ _).mp this

private theorem open_normalization_iso
    {U C : Scheme.{u}} [IsIntegral C] [Nonempty U]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
    (hnormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) :
    IsIso j.fromNormalization := by
  have : IsIso C.fromSpecFunctionField.fromNormalization :=
    normal_generic_normalization_iso C hnormal
  let a := C.fromSpecFunctionField.normalizationDesc
    (FiniteEtale.genericPointLift j ≫ j.toNormalization) j.fromNormalization (by
      rw [Category.assoc, Hom.toNormalization_fromNormalization,
        FiniteEtale.genericPointLift_comp])
  let s := inv C.fromSpecFunctionField.fromNormalization ≫ a
  have hs : s ≫ j.fromNormalization = 𝟙 C := by
    simp only [s, a, Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  have hsnd : IsIso (pullback.snd j.fromNormalization j) := by
    have : IsIso (pullback.snd j j).fromNormalization := by
      have : IsIso ((pullback.snd j j).toNormalization ≫
          (pullback.snd j j).fromNormalization) := by
        rw [Hom.toNormalization_fromNormalization]
        infer_instance
      exact (isIso_comp_left_iff _ _).mp this
    have : IsIso (j.normalizationPullback j ≫ pullback.snd j.fromNormalization j) := by
      rw [Hom.normalizationPullback_snd]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp this
  have hj : j ≫ s = j.toNormalization := by
    let t₁ : U ⟶ pullback j.fromNormalization j :=
      pullback.lift (j ≫ s) (𝟙 U) (by rw [Category.assoc, hs]; simp)
    let t₂ : U ⟶ pullback j.fromNormalization j :=
      pullback.lift j.toNormalization (𝟙 U) (by
      rw [Hom.toNormalization_fromNormalization]; simp)
    have ht : t₁ = t₂ := by
      apply (cancel_mono (pullback.snd j.fromNormalization j)).mp
      simp [t₁, t₂]
    have := congrArg (· ≫ pullback.fst j.fromNormalization j) ht
    simpa [t₁, t₂] using this
  have hns : j.fromNormalization ≫ s = 𝟙 j.normalization := by
    apply Hom.normalization.hom_ext j _ _ j.fromNormalization
    · simp only [← Category.assoc, Hom.toNormalization_fromNormalization, hj,
        Category.comp_id]
    · rw [Category.assoc, hs, Category.comp_id]
    · exact Category.id_comp _
  exact ⟨⟨s, hns, hs⟩⟩

private theorem isIso_normalizationDesc_of_isIso_fromNormalization
    {X T Y : Scheme.{u}} (h : X ⟶ T) (g : T ⟶ Y)
    [QuasiCompact h] [QuasiSeparated h] [IsIntegralHom g]
    [IsIso h.fromNormalization] :
    IsIso ((h ≫ g).normalizationDesc h g rfl) := by
  let f := h ≫ g
  let d : f.normalization ⟶ T := f.normalizationDesc h g rfl
  have hd : f.toNormalization ≫ d = h :=
    Hom.toNormalization_normalizationDesc f h g rfl
  let a : h.normalization ⟶ f.normalization :=
    h.normalizationDesc f.toNormalization d hd.symm
  have ha : a ≫ d = h.fromNormalization :=
    Hom.normalizationDesc_comp h f.toNormalization d hd.symm
  let i : T ⟶ f.normalization := inv h.fromNormalization ≫ a
  have hid : i ≫ d = 𝟙 T := by
    simp only [i, Category.assoc, ha, IsIso.inv_hom_id]
  have hi : h ≫ i = f.toNormalization := by
    have hh : h ≫ inv h.fromNormalization = h.toNormalization := by
      apply (cancel_mono h.fromNormalization).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Hom.toNormalization_fromNormalization]
    dsimp only [i]
    rw [← Category.assoc, hh]
    exact Hom.toNormalization_normalizationDesc h f.toNormalization d hd.symm
  have hdg : d ≫ g = f.fromNormalization :=
    Hom.normalizationDesc_comp f h g rfl
  have hig : i ≫ f.fromNormalization = g := by
    rw [← hdg, ← Category.assoc, hid, Category.id_comp]
  have hdi : d ≫ i = 𝟙 f.normalization := by
    apply Hom.normalization.hom_ext f _ _ f.fromNormalization
    · simp only [← Category.assoc, hd, hi, Category.comp_id]
    · rw [Category.assoc, hig, hdg]
    · exact Category.id_comp _
  exact ⟨⟨i, hdi, hid⟩⟩

private theorem normalization_iso_of_source_iso
    {X X' C : Scheme.{u}} (f : X ⟶ C) (f' : X' ⟶ C)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (e : X ≅ X') (he : e.hom ≫ f' = f) :
    ∃ i : f.normalization ≅ f'.normalization,
      i.hom ≫ f'.fromNormalization = f.fromNormalization := by
  have he' : e.inv ≫ f = f' := by rw [← he, e.inv_hom_id_assoc]
  let a := f.normalizationDesc (e.hom ≫ f'.toNormalization) f'.fromNormalization (by
    rw [Category.assoc, Hom.toNormalization_fromNormalization, he])
  let b := f'.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization (by
    rw [Category.assoc, Hom.toNormalization_fromNormalization, he'])
  have ha : a ≫ f'.fromNormalization = f.fromNormalization :=
    Hom.normalizationDesc_comp _ _ _ _
  have hb : b ≫ f.fromNormalization = f'.fromNormalization :=
    Hom.normalizationDesc_comp _ _ _ _
  have hta : f.toNormalization ≫ a = e.hom ≫ f'.toNormalization :=
    Hom.toNormalization_normalizationDesc _ _ _ _
  have htb : f'.toNormalization ≫ b = e.inv ≫ f.toNormalization :=
    Hom.toNormalization_normalizationDesc _ _ _ _
  have hab : a ≫ b = 𝟙 f.normalization := by
    apply Hom.normalization.hom_ext f _ _ f.fromNormalization
    · rw [← Category.assoc, hta, Category.assoc, htb, e.hom_inv_id_assoc,
        Category.comp_id]
    · rw [Category.assoc, hb, ha]
    · exact Category.id_comp _
  have hba : b ≫ a = 𝟙 f'.normalization := by
    apply Hom.normalization.hom_ext f' _ _ f'.fromNormalization
    · rw [← Category.assoc, htb, Category.assoc, hta, e.inv_hom_id_assoc,
        Category.comp_id]
    · rw [Category.assoc, ha, hb]
    · exact Category.id_comp _
  exact ⟨⟨a, b, hab, hba⟩, ha⟩

private theorem normalization_finite_etale_of_source_iso
    {X X' C : Scheme.{u}} (f : X ⟶ C) (f' : X' ⟶ C)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (e : X ≅ X') (he : e.hom ≫ f' = f)
    [IsFinite f'.fromNormalization] [Etale f'.fromNormalization] :
    IsFinite f.fromNormalization ∧ Etale f.fromNormalization := by
  obtain ⟨i, hi⟩ := normalization_iso_of_source_iso f f' e he
  constructor <;> rw [← hi] <;> infer_instance

private theorem normalization_of_open_model_is_finite_etale
    {V H : Scheme.{u}} [IsIntegral H] [Nonempty V]
    (j : V ⟶ H) [IsOpenImmersion j] [QuasiCompact j]
    (hnormal : ∀ x : H, IsIntegrallyClosed (H.presheaf.stalk x))
    (P : V.FiniteEtale) (Q : H.FiniteEtale)
    [IsFinite P.obj.hom] [Etale P.obj.hom]
    [IsFinite Q.obj.hom] [Etale Q.obj.hom]
    (e : (FiniteEtale.pullback j).obj Q ≅ P) :
    IsFinite (P.obj.hom ≫ j).fromNormalization ∧
      Etale (P.obj.hom ≫ j).fromNormalization := by
  have : IsIso j.fromNormalization := open_normalization_iso j hnormal
  let h := pullback.snd j Q.obj.hom
  have : IsIso h.fromNormalization := by
    dsimp only [h]
    rw [← Hom.normalizationPullback_snd j Q.obj.hom]
    infer_instance
  let d := (h ≫ Q.obj.hom).normalizationDesc h Q.obj.hom rfl
  have : IsIso d := isIso_normalizationDesc_of_isIso_fromNormalization h Q.obj.hom
  have hd : d ≫ Q.obj.hom = (h ≫ Q.obj.hom).fromNormalization :=
    Hom.normalizationDesc_comp _ _ _ rfl
  have : IsFinite (h ≫ Q.obj.hom).fromNormalization := by rw [← hd]; infer_instance
  have : Etale (h ≫ Q.obj.hom).fromNormalization := by rw [← hd]; infer_instance
  let forget : V.FiniteEtale ⥤ Scheme.{u} :=
    ObjectProperty.ι _ ⋙ MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _
  let i : P.obj.left ≅ pullback j Q.obj.hom :=
    forget.mapIso e.symm ≪≫ pullbackSymmetry Q.obj.hom j
  have hi : i.hom ≫ (h ≫ Q.obj.hom) = P.obj.hom ≫ j := by
    change e.inv.hom.left ≫ (pullbackSymmetry Q.obj.hom j).hom ≫
      pullback.snd j Q.obj.hom ≫ Q.obj.hom = P.obj.hom ≫ j
    simp only [pullbackSymmetry_hom_comp_snd_assoc]
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ j) (FiniteEtale.hom_left_comp e.inv)
  exact normalization_finite_etale_of_source_iso _ _ i hi

set_option backward.defeqAttrib.useBackward true in
open TensorProduct in
private theorem normalizationPullback_affine_indEtale {X C Y : Scheme.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : C.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U)
    (hS : RingHom.IndEtaleAcrossUniverses (g.appLE U V hVU).hom) :
    IsIso (f.normalizationPullback g ∣_ (pullback.snd f.fromNormalization g ⁻¹ᵁ V)) := by
  let W := pullback.snd f.fromNormalization g ⁻¹ᵁ V
  refine (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(C, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(C, U)] integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (RingHom.integralClosure_bijective_of_indEtale hS)
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

private theorem normalizationPullback_affine_indEtale_global
    {X C Y : Scheme.{u}} [IsAffine C] [IsAffine Y]
    (f : X ⟶ C) (g : Y ⟶ C) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    (hS : RingHom.IndEtaleAcrossUniverses (g.appLE ⊤ ⊤ (by simp)).hom) :
    IsIso (f.normalizationPullback g) := by
  have h := normalizationPullback_affine_indEtale f g (isAffineOpen_top C)
    (isAffineOpen_top Y) (by simp) hS
  have htop : IsIso (f.normalizationPullback g ∣_ ⊤) := by simpa using h
  exact IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _) fun x ↦ ⟨⊤, trivial, htop⟩

private theorem indEtale_across_iff {A B : Type u} [CommRing A] [CommRing B]
    (a : A →+* B) : a.IndEtaleAcrossUniverses ↔ a.IndEtale := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  constructor
  · intro h
    exact hi.2 _ (ULift.ringEquiv.symm : A ≃+* ULift.{u} A)
      (hi.1 _ (ULift.ringEquiv : ULift.{u} B ≃+* B) h)
  · intro h
    exact hi.1 _ (ULift.ringEquiv.symm : B ≃+* ULift.{u} B)
      (hi.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A) h)

private theorem indEtale_specMap_appLE
    {A H : Type u} [CommRing A] [CommRing H]
    (a : A →+* H) (ha : a.IndEtale) :
    RingHom.IndEtaleAcrossUniverses
      ((Spec.map (CommRingCat.ofHom a)).appLE ⊤ ⊤ (by simp)).hom := by
  have hi : RingHom.RespectsIso (@RingHom.IndEtale.{u}) :=
    RingHom.IndEtale.isStableUnderBaseChange.localizationPreserves.away.respectsIso
  have happ : (Spec.map (CommRingCat.ofHom a)).appTop =
      (ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom a ≫ (ΓSpecIso (.of H)).inv := by
    rw [← cancel_mono (ΓSpecIso (.of H)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ΓSpecIso_naturality _
  apply (indEtale_across_iff _).mpr
  change (Spec.map (CommRingCat.ofHom a)).appTop.hom.IndEtale
  rw [happ, CommRingCat.hom_comp, CommRingCat.hom_comp]
  exact hi.1 _ (ΓSpecIso (.of H)).symm.commRingCatIsoToRingEquiv
    (hi.2 _ (ΓSpecIso (.of A)).commRingCatIsoToRingEquiv ha)

private theorem finite_etale_descends_specMap
    {A H : Type u} [CommRing A] [CommRing H] [Algebra A H]
    [Module.FaithfullyFlat A H]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hfin : IsFinite (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A H)))))
    (het : Etale (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap A H))))) :
    IsFinite f ∧ Etale f := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A H))
  have hg := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A H))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat g := hg.1
  have : Surjective g := hg.2
  have hcover : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Spec (.of H)) (fun _ ↦ g) ∈
      Scheme.fpqcPrecoverage (Spec (.of A)) := by
    rw [Presieve.ofArrows_pUnit]
    exact g.singleton_mem_fpqcPrecoverage
  exact ⟨isFinite_of_fpqc_cover f _ _ hcover (fun _ ↦ hfin),
    etale_of_fpqc_cover f _ _ hcover (fun _ ↦ het)⟩

private theorem open_extension_of_indEtale_model
    (A H : Type u) [CommRing A] [CommRing H] [IsDomain H] [IsIntegrallyClosed H]
    [Algebra A H] [Algebra.IndEtale A H] [Module.FaithfullyFlat A H]
    {V : Scheme.{u}} (j : V ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (hne : Nonempty (pullback j
      (Spec.map (CommRingCat.ofHom (algebraMap A H))) : Scheme.{u}))
    (P : V.FiniteEtale) (Q : (Spec (.of H)).FiniteEtale)
    (e : (FiniteEtale.pullback
      (pullback.snd j (Spec.map (CommRingCat.ofHom (algebraMap A H))))).obj Q ≅
        (FiniteEtale.pullback
      (pullback.fst j (Spec.map (CommRingCat.ofHom (algebraMap A H))))).obj P) :
    ∃ Q' : (Spec (.of A)).FiniteEtale,
      Nonempty ((FiniteEtale.pullback j).obj Q' ≅ P) := by
  have : IsFinite P.obj.hom := P.property
  have : Etale P.obj.hom := P.obj.prop
  have : IsFinite Q.obj.hom := Q.property
  have : Etale Q.obj.hom := Q.obj.prop
  let g := Spec.map (CommRingCat.ofHom (algebraMap A H))
  have hg := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A H))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat g := hg.1
  have : Nonempty (pullback j g : Scheme.{u}) := hne
  let jh := pullback.snd j g
  let Ph := (FiniteEtale.pullback (pullback.fst j g)).obj P
  have : IsFinite Ph.obj.hom := Ph.property
  have : Etale Ph.obj.hom := Ph.obj.prop
  have hn := normalization_of_open_model_is_finite_etale jh
    (Scheme.isIntegrallyClosed_stalk_Spec H) Ph Q e
  have : IsFinite (Ph.obj.hom ≫ jh).fromNormalization := hn.1
  have : Etale (Ph.obj.hom ≫ jh).fromNormalization := hn.2
  let f := P.obj.hom ≫ j
  let i : pullback f g ≅ Ph.obj.left :=
    (pullbackRightPullbackFstIso j g P.obj.hom).symm
  have hi : i.hom ≫ (Ph.obj.hom ≫ jh) = pullback.snd f g :=
    pullbackRightPullbackFstIso_inv_snd_snd j g P.obj.hom
  have hbase := normalization_finite_etale_of_source_iso (pullback.snd f g)
    (Ph.obj.hom ≫ jh) i hi
  have : IsFinite (pullback.snd f g).fromNormalization := hbase.1
  have : Etale (pullback.snd f g).fromNormalization := hbase.2
  have : IsIso (f.normalizationPullback g) := normalizationPullback_affine_indEtale_global
    f g (indEtale_specMap_appLE _ ((RingHom.IndEtale.algebraMap_iff A H).mpr inferInstance))
  have hproj : pullback.snd f.fromNormalization g =
      inv (f.normalizationPullback g) ≫ (pullback.snd f g).fromNormalization := by
    rw [IsIso.eq_inv_comp]
    exact Hom.normalizationPullback_snd f g
  have hfin : IsFinite (pullback.snd f.fromNormalization g) := by
    rw [hproj]
    infer_instance
  have het : Etale (pullback.snd f.fromNormalization g) := by
    rw [hproj]
    infer_instance
  obtain ⟨hfin, het⟩ := finite_etale_descends_specMap f.fromNormalization hfin het
  have : IsFinite f.fromNormalization := hfin
  have : Etale f.fromNormalization := het
  let Q' : (Spec (.of A)).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ f.fromNormalization het, hfin⟩
  refine ⟨Q', ⟨?_⟩⟩
  exact ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk
    (Hom.pullbackFromNormalizationIso P.obj.hom j)
    (Hom.pullbackFromNormalizationIso_hom_comp P.obj.hom j))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteEtale

private theorem generic_pullback_full {C : Scheme.{u}} [IsIntegral C]
    (hnormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) :
    (Scheme.FiniteEtale.pullback C.fromSpecFunctionField).Full := by
  constructor
  intro P Q f
  have : IsFinite P.obj.hom := P.property
  have : IsFinite Q.obj.hom := Q.property
  have : Etale P.obj.hom := P.obj.prop
  have : Etale Q.obj.hom := Q.obj.prop
  obtain ⟨g, ⟨hg, hgf⟩, _⟩ := finiteEtale_normalIntegral_generic_hom_full hnormal
    P.obj.hom Q.obj.hom (Limits.pullback.snd _ C.fromSpecFunctionField)
    (Limits.pullback.snd _ C.fromSpecFunctionField)
    (Limits.pullback.fst _ C.fromSpecFunctionField)
    (Limits.pullback.fst _ C.fromSpecFunctionField)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
    f.hom.left (hom_left_comp f)
  let gg : P ⟶ Q := ObjectProperty.homMk (MorphismProperty.Over.homMk g hg)
  refine ⟨gg, ?_⟩
  apply hom_ext
  rw [pullback_map_hom_left]
  apply Limits.pullback.hom_ext
  · simpa [Limits.pullback.map, gg] using hgf
  · simpa [Limits.pullback.map] using (hom_left_comp f).symm

private theorem fraction_generic_factor
    (H K : Type u) [CommRing H] [IsDomain H] [Field K]
    [Algebra H K] [IsFractionRing H K] :
    ∃ e : Spec (.of K) ≅ Spec (Spec (.of H)).functionField,
      e.hom ≫ (Spec (.of H)).fromSpecFunctionField =
        Spec.map (CommRingCat.ofHom (algebraMap H K)) := by
  let : Algebra H (Spec (.of H)).functionField :=
    instAlgebraCarrierFunctionFieldSpec (.of H)
  have : IsFractionRing H (Spec (.of H)).functionField :=
    functionField_isFractionRing_of_affine (.of H)
  let e := IsLocalization.algEquiv (nonZeroDivisors H) (Spec (.of H)).functionField K
  let i := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  refine ⟨i, ?_⟩
  change i.hom ≫ (Spec (.of H)).fromSpecStalk _ = _
  rw [Spec.fromSpecStalk_eq']
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

private theorem generic_lift_factor
    {U C : Scheme.{u}} [IsIntegral C] [IsIntegral U]
    (j : U ⟶ C) [IsOpenImmersion j] :
    genericPointLift j = Spec.map j.functionFieldIso.inv ≫ U.fromSpecFunctionField := by
  apply (cancel_mono j).mp
  rw [genericPointLift_comp, Category.assoc]
  simp only [Scheme.Hom.functionFieldIso, Iso.trans_inv, asIso_inv, Spec.map_comp,
    Category.assoc, TopCat.Presheaf.stalkCongr_inv,
    Spec.map_inv]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk (f := j),
    IsIso.inv_hom_id_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

private theorem generic_pullback_faithful {C : Scheme.{u}} [IsIntegral C] :
    (pullback C.fromSpecFunctionField).Faithful := by
  let s := Spec.map (CommRingCat.ofHom
    (algebraMap C.functionField (AlgebraicClosure C.functionField)))
  exact Functor.Faithful.of_comp_iso (pullbackFiberIso C.fromSpecFunctionField s)

private theorem iso_of_fraction_generic_iso
    (H K : Type u) [CommRing H] [IsDomain H] [IsIntegrallyClosed H]
    [Field K] [Algebra H K] [IsFractionRing H K]
    {V : Scheme.{u}} [Nonempty V]
    (j : V ⟶ Spec (.of H)) [IsOpenImmersion j]
    (a : Spec (.of K) ⟶ V)
    (ha : a ≫ j = Spec.map (CommRingCat.ofHom (algebraMap H K)))
    (P Q : V.FiniteEtale) (eη : (pullback a).obj P ≅ (pullback a).obj Q) :
    Nonempty (P ≅ Q) := by
  have : IsIntegral V := isIntegral_of_isOpenImmersion j
  obtain ⟨i, hi⟩ := fraction_generic_factor H K
  let d := Scheme.Spec.mapIso j.functionFieldIso.symm.op
  let e := i ≪≫ d
  have hfac : Spec.map j.functionFieldIso.inv ≫ V.fromSpecFunctionField ≫ j =
      (Spec (.of H)).fromSpecFunctionField := by
    rw [← Category.assoc, ← generic_lift_factor j, genericPointLift_comp]
  have he : e.hom ≫ V.fromSpecFunctionField = a := by
    apply (cancel_mono j).mp
    change (i.hom ≫ Spec.map j.functionFieldIso.inv) ≫ V.fromSpecFunctionField ≫ j = a ≫ j
    rw [Category.assoc, hfac, hi, ha]
  have hea : e.inv ≫ a = V.fromSpecFunctionField := by
    rw [← he, e.inv_hom_id_assoc]
  let c (Z : V.FiniteEtale) :
      (pullback V.fromSpecFunctionField).obj Z ≅ (pullback e.inv).obj ((pullback a).obj Z) :=
    eqToIso (congrArg (fun f ↦ (pullback f).obj Z) hea.symm) ≪≫ pullbackCompIso _ _ Z
  have hn (v : V) : IsIntegrallyClosed (V.presheaf.stalk v) := by
    have := Scheme.isIntegrallyClosed_stalk_Spec H (j v)
    exact IsIntegrallyClosed.of_equiv (asIso (j.stalkMap v)).commRingCatIsoToRingEquiv
  have : (pullback V.fromSpecFunctionField).Full := generic_pullback_full hn
  have : (pullback V.fromSpecFunctionField).Faithful := generic_pullback_faithful
  exact ⟨(pullback V.fromSpecFunctionField).preimageIso
    (c P ≪≫ (pullback e.inv).mapIso eη ≪≫ (c Q).symm)⟩

private theorem henselization_faithfullyFlat
    (A H : Type u) [CommRing A] [IsLocalRing A]
    [CommRing H] [HenselianLocalRing H] [Algebra A H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H) :
    Module.FaithfullyFlat A H := by
  have hind := RingHom.henselization_prime_indEtale A (IsLocalRing.maximalIdeal A) H hH
  rw [← IsScalarTower.algebraMap_eq A
    (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H] at hind
  have : Algebra.IndEtale A H := (RingHom.IndEtale.algebraMap_iff A H).mp hind
  have : Algebra.WeaklyEtale A H := inferInstance
  have : Module.Flat A H := inferInstance
  have : IsLocalHom (algebraMap A
      (Localization.AtPrime (IsLocalRing.maximalIdeal A))) := by
    constructor
    intro a ha
    exact IsLocalRing.notMem_maximalIdeal.mp
      ((IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime (IsLocalRing.maximalIdeal A))
        (IsLocalRing.maximalIdeal A) a).mp ha)
  have : IsLocalHom (algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H) := hH.1
  have : IsLocalHom (algebraMap A H) := by
    rw [IsScalarTower.algebraMap_eq A
      (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    infer_instance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

private theorem henselization_normal
    (A H : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing H] [HenselianLocalRing H] [Algebra A H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (IsLocalRing.maximalIdeal A) H) :
    IsIntegrallyClosed H := by
  have hind := RingHom.henselization_prime_indEtale A (IsLocalRing.maximalIdeal A) H hH
  rw [← IsScalarTower.algebraMap_eq A
    (Localization.AtPrime (IsLocalRing.maximalIdeal A)) H] at hind
  have : Algebra.IndEtale A H := (RingHom.IndEtale.algebraMap_iff A H).mp hind
  obtain ⟨I, hI, hfilter, P, hP⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := A) (S := H)
  let : SmallCategory I := hI
  let : IsFiltered I := hfilter
  let e := (colimit.isColimit P.diag).coconePointUniqueUpToIso P.isColimit
  let er : ↥(colimit P.diag) ≃+* H := (CommAlgCat.algEquivOfIso e).toRingEquiv
  have : IsLocalRing ↥(colimit P.diag) := er.symm.isLocalRing
  obtain ⟨⟨hdomain, hclosed⟩, _⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit A
      (fun p _ ↦ ⟨inferInstance,
        isIntegrallyClosed_of_isLocalization _ p.primeCompl
          p.primeCompl_le_nonZeroDivisors⟩) P.diag hP
  have := hclosed
  exact IsIntegrallyClosed.of_equiv er

private theorem extension_of_henselian_generic_model
    (A H K : Type u) [CommRing A] [CommRing H] [IsDomain H] [IsIntegrallyClosed H]
    [Algebra A H] [Algebra.IndEtale A H] [Module.FaithfullyFlat A H]
    [Field K] [Algebra H K] [IsFractionRing H K]
    {V : Scheme.{u}} (j : V ⟶ Spec (.of A)) [IsOpenImmersion j] [QuasiCompact j]
    (a : Spec (.of K) ⟶ Limits.pullback j
      (Spec.map (CommRingCat.ofHom (algebraMap A H))))
    (ha : a ≫ Limits.pullback.snd j
      (Spec.map (CommRingCat.ofHom (algebraMap A H))) =
        Spec.map (CommRingCat.ofHom (algebraMap H K)))
    (P : V.FiniteEtale) (Q : (Spec (.of H)).FiniteEtale)
    (e : (pullback (Spec.map (CommRingCat.ofHom (algebraMap H K)))).obj Q ≅
      (pullback (a ≫ Limits.pullback.fst j
        (Spec.map (CommRingCat.ofHom (algebraMap A H))))).obj P) :
    ∃ Q' : (Spec (.of A)).FiniteEtale, Nonempty ((pullback j).obj Q' ≅ P) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap A H))
  have hne : Nonempty (Limits.pullback j g : Scheme.{u}) := ⟨a (IsLocalRing.closedPoint K)⟩
  have : Nonempty (Limits.pullback j g : Scheme.{u}) := hne
  let jh := Limits.pullback.snd j g
  let Ph := (pullback (Limits.pullback.fst j g)).obj P
  let eg : (pullback a).obj ((pullback jh).obj Q) ≅ (pullback a).obj Ph :=
    (pullbackCompIso a jh Q).symm ≪≫
      eqToIso (congrArg (fun f ↦ (pullback f).obj Q) ha) ≪≫
      e ≪≫ pullbackCompIso a (Limits.pullback.fst j g) P
  obtain ⟨i⟩ := iso_of_fraction_generic_iso H K jh a ha
    ((pullback jh).obj Q) Ph eg
  exact open_extension_of_indEtale_model A H j hne P Q i

/-- A finite etale model of the henselian generic restriction descends to the ordinary
stalk, with its prescribed comparison on the open overlap. The conclusion does not
spread the model to an open neighbourhood or glue it to the original cover.

Source: Stacks Project, Tag 0BSM, normalization and faithfully flat descent in the
proof; Tag 0CBF, integral closure under ind-etale base change; Tags 02LA and 02VN,
fpqc descent of finiteness and etaleness.
(blueprint: lem-dl-a1-henselian-finite-etale-stalk-model).

Proof:
1. Set A = C.stalk(x) and h = Spec B.H -> Spec A. The henselization universal
property gives the ind-etale A-algebra B.H. It is flat and local, hence faithfully
flat. Normality of A and the etale colimit description give normality of B.H.
2. Restrict P to the local open Spec A times_C U and base change to B.H. The
specified localGenericPoint and B.localGenericPoint_spec lift Spec B.K to this
nonempty open of Spec B.H. The fraction-ring equivalence and the function-field
isomorphism for an open immersion identify this map with the generic point.
Normality of B.H gives normality of the overlap. Generic full faithfulness lifts
the given generic comparison to an isomorphism of finite etale covers there.
3. Normalize Spec A in this restricted cover. Integral closure commutes with the
ind-etale base change A -> B.H (0CBF). The generic comparison identifies the
base-changed normalization with the supplied finite etale B.H-cover: a finite
etale algebra over a normal ring is the integral closure in its generic algebra.
This works componentwise, also for disconnected or empty covers.
4. Finiteness and etaleness descend along the faithfully flat map h, so this
normalization is finite etale over Spec A. Over the punctured local open it is P:
P is already finite etale over a normal scheme and hence already normal.
5. Pull the resulting cover back through the canonical isomorphism from
C times_C Spec A to Spec A. Normalize the open immersion j by j.isoOpensRange.
Pullback associativity and the comparison of step 4 give exactly the two
pullbacks over the local overlap in the conclusion. These comparisons preserve
both projections, so no choice of a generic isomorphism changes the claimed
extension of P. No global extension or kernel-generation assertion is used.
-/
theorem stalk_model_of_henselian_model
    {U C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C]
    (j : U ⟶ C) [IsOpenImmersion j]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (x : C) (B : HenselianBoundaryLocalData j b x)
    (hnormal : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y))
    (P : U.FiniteEtale)
    (hmodel : ∃ Q : (Spec (.of B.H)).FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)))).obj Q ≅
          (Scheme.FiniteEtale.pullback B.localGenericPoint).obj P)) :
    ∃ Q : (Limits.pullback (𝟙 C) (C.fromSpecStalk x)).FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback
        (Limits.pullback.fst ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
          (Limits.pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj
            ((Scheme.FiniteEtale.pullback j.isoOpensRange.inv).obj P) ≅
        (Scheme.FiniteEtale.pullback
        (Limits.pullback.snd ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
          (Limits.pullback.fst (𝟙 C) (C.fromSpecStalk x)))).obj Q) := by
  let A : Type u := C.presheaf.stalk x
  have : IsIntegrallyClosed A := hnormal x
  have : IsIntegrallyClosed B.H := henselization_normal A B.H B.isHenselization
  have hind := RingHom.henselization_prime_indEtale A (IsLocalRing.maximalIdeal A)
    B.H B.isHenselization
  rw [← IsScalarTower.algebraMap_eq A
    (Localization.AtPrime (IsLocalRing.maximalIdeal A)) B.H] at hind
  have : Algebra.IndEtale A B.H := (RingHom.IndEtale.algebraMap_iff A B.H).mp hind
  have : Module.FaithfullyFlat A B.H :=
    henselization_faithfullyFlat A B.H B.isHenselization
  let c := C.fromSpecStalk x
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B.H))
  let jA := Limits.pullback.snd j c
  let PA := (pullback (Limits.pullback.fst j c)).obj P
  let t : Spec (.of B.K) ⟶ Limits.pullback j c :=
    Limits.pullback.lift B.localGenericPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A B.K))) B.localGenericPoint_spec
  have htg : t ≫ jA = Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)) ≫ g := by
    dsimp only [t, jA, g]
    rw [Limits.pullback.lift_snd, IsScalarTower.algebraMap_eq A B.H B.K,
      CommRingCat.ofHom_comp, Spec.map_comp]
  let a : Spec (.of B.K) ⟶ Limits.pullback jA g :=
    Limits.pullback.lift t (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K))) htg
  have ha : a ≫ Limits.pullback.snd jA g =
      Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)) := by simp [a]
  have hgen : (a ≫ Limits.pullback.fst jA g) ≫ Limits.pullback.fst j c =
      B.localGenericPoint := by simp [a, t]
  obtain ⟨QH, ⟨eH⟩⟩ := hmodel
  let eg : (pullback (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)))).obj QH ≅
      (pullback (a ≫ Limits.pullback.fst jA g)).obj PA :=
    eH ≪≫ eqToIso (congrArg (fun f ↦ (pullback f).obj P) hgen.symm) ≪≫
      pullbackCompIso _ _ P
  obtain ⟨QA, ⟨eA⟩⟩ := extension_of_henselian_generic_model A B.H B.K jA a ha PA QH eg
  let sA := Limits.pullback.snd (𝟙 C) c
  let QS := (pullback sA).obj QA
  let kU := Limits.pullback.fst ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
    (Limits.pullback.fst (𝟙 C) c)
  let kS := Limits.pullback.snd ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
    (Limits.pullback.fst (𝟙 C) c)
  have h2 : Limits.pullback.fst (𝟙 C) c = sA ≫ c := by
    simpa only [Category.comp_id] using (Limits.pullback.condition (f := 𝟙 C) (g := c))
  have hcone : (kU ≫ j.isoOpensRange.inv) ≫ j = (kS ≫ sA) ≫ c := by
    simpa only [kU, kS, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, h2,
      Scheme.Hom.id_preimage] using
      (Limits.pullback.condition (f := ((𝟙 C) ⁻¹ᵁ j.opensRange).ι)
        (g := Limits.pullback.fst (𝟙 C) c))
  let l : Limits.pullback ((𝟙 C) ⁻¹ᵁ j.opensRange).ι
      (Limits.pullback.fst (𝟙 C) c) ⟶ Limits.pullback j c :=
    Limits.pullback.lift (kU ≫ j.isoOpensRange.inv) (kS ≫ sA) hcone
  refine ⟨QS, ⟨?_⟩⟩
  exact (pullbackCompIso kU j.isoOpensRange.inv P).symm ≪≫
    eqToIso (congrArg (fun f ↦ (pullback f).obj P)
      (Limits.pullback.lift_fst (kU ≫ j.isoOpensRange.inv) (kS ≫ sA) hcone).symm) ≪≫
    pullbackCompIso l (Limits.pullback.fst j c) P ≪≫
    (pullback l).mapIso eA.symm ≪≫ (pullbackCompIso l jA QA).symm ≪≫
    eqToIso (congrArg (fun f ↦ (pullback f).obj QA)
      (Limits.pullback.lift_snd (kU ≫ j.isoOpensRange.inv) (kS ≫ sA) hcone)) ≪≫
    pullbackCompIso kS sA QA

end AlgebraicGeometry.Scheme.FiniteEtale
