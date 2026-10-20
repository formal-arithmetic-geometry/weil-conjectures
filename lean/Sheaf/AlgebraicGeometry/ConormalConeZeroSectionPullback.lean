/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.ReesConeNormalization

/-! # The conormal relative-Spec zero section pulls back by augmentation

Source: Stacks 01LX and 0630; the definitions of the conormal augmentation and its
contravariant relative-Spec section.
(blueprint: lem-pur-conormal-zero-section-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem sheaf_eqToHom_app {T : TopCat.{u}}
    {A B : TopCat.Sheaf CommRingCat.{u} T} (e : A = B) (W : TopologicalSpace.Opens T) :
    (eqToHom e).hom.app (op W) = eqToHom (by cases e; rfl) := by
  cases e
  rfl

private theorem transport_app {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T}
    {A B C D F : Under R} (e : B = D) (e' : C = F)
    (k : B ⟶ C) (c : A ⟶ B) (U : TopologicalSpace.Opens T)
    (p : D.right.obj.obj (op U) ⟶ F.right.obj.obj (op U))
    (hm : k.right.hom.app (op U) =
      eqToHom (congrArg (fun X : Under R ↦ X.right.obj.obj (op U)) e) ≫ p ≫
        eqToHom (congrArg (fun X : Under R ↦ X.right.obj.obj (op U)) e'.symm)) :
    (c ≫ k ≫ eqToHom e').right.hom.app (op U) =
      (c ≫ eqToHom e).right.hom.app (op U) ≫ p := by
  subst D
  subst F
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    Under.comp_right, TopCat.Sheaf.comp_app] using
    congrArg (fun t ↦ c.right.hom.app (op U) ≫ t) hm

private theorem transport_augmentation_app {T : TopCat.{u}}
    {R : TopCat.Sheaf CommRingCat.{u} T} {A B C D : Under R}
    (e : B = D) (e' : C = Under.mk (𝟙 R)) (k : B ⟶ C) (c : A ⟶ B)
    (a : A ⟶ Under.mk (𝟙 R)) (U : TopologicalSpace.Opens T)
    (p : D.right.obj.obj (op U) ⟶ R.obj.obj (op U))
    (hm : k.right.hom.app (op U) =
      eqToHom (congrArg (fun X : Under R ↦ X.right.obj.obj (op U)) e) ≫ p ≫
        eqToHom (congrArg (fun X : Under R ↦ X.right.obj.obj (op U)) e'.symm))
    (he : c ≫ k = a ≫ Under.homMk C.hom (Category.id_comp _)) :
    (c ≫ eqToHom e).right.hom.app (op U) ≫ p = a.right.hom.app (op U) := by
  have ha : a ≫ Under.homMk C.hom (Category.id_comp _) ≫ eqToHom e' = a := by
    apply Under.UnderMorphism.ext
    simp only [Under.comp_right, Under.homMk_right]
    rw [(eqToHom e').w]
    exact Category.comp_id _
  have ht := congrArg (fun t : A ⟶ C ↦
    (t ≫ eqToHom e').right.hom.app (op U)) he
  have hr := congrArg (fun t : A ⟶ Under.mk (𝟙 R) ↦ t.right.hom.app (op U)) ha
  exact (transport_app e e' k c U p hm).symm.trans (ht.trans hr)

private theorem fullSubcategory_iso_cancel {C : Type*} [Category C]
    {P : ObjectProperty C} {X Y Z : P.FullSubcategory} (e : X ≅ Y)
    (a : Y.obj ⟶ Z.obj) (k : X ⟶ Z)
    (hk : k = e.hom ≫ ObjectProperty.homMk a) : e.inv.hom ≫ k.hom = a := by
  subst k
  change e.inv.hom ≫ e.hom.hom ≫ a = a
  rw [← Category.assoc]
  have he := congrArg (fun f : Y ⟶ Y ↦ f.hom) e.inv_hom_id
  change e.inv.hom ≫ e.hom.hom = 𝟙 Y.obj at he
  rw [he, Category.id_comp]

private theorem relativeSpec_obj (S : Scheme.{u})
    (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom)) :
    ((VectorBundleZeroSection.antiEquivalence S).functor.obj (op Y)).obj =
      Under.mk (⟨Y.obj.hom.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} Y.obj.hom.base).obj Y.obj.left.sheaf) := by
  rfl

private theorem relativeSpec_map (S : Scheme.{u})
    (Y Y' : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
    (h : Y ⟶ Y') (U : S.Opens) :
    (((VectorBundleZeroSection.antiEquivalence S).functor.map h.op).hom).right.hom.app
        (op U) =
      eqToHom (by rw [relativeSpec_obj S Y']; rfl) ≫
        h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ U) (Y.obj.hom ⁻¹ᵁ U)
          (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
        eqToHom (by rw [relativeSpec_obj S Y]; rfl) := by
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem functor_section_app (S : Scheme.{u})
    {P : ObjectProperty S.CommAlgebraSheaf}
    (F : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ⥤
      P.FullSubcategory)
    (hobj : ∀ Y, (F.obj (op Y)).obj =
      Under.mk (⟨Y.obj.hom.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} Y.obj.hom.base).obj Y.obj.left.sheaf))
    {A : S.CommAlgebraSheaf}
    (Y : ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
    (h : VectorBundleZeroSection.baseObject S ⟶ Y)
    (c : A ⟶ (F.obj (op Y)).obj) (a : A ⟶ Under.mk (𝟙 S.sheaf))
    (U : S.Opens)
    (hm : (F.map h.op).hom.right.hom.app (op U) =
      eqToHom (by rw [hobj Y]; rfl) ≫
        h.hom.left.appLE (Y.obj.hom ⁻¹ᵁ U)
          ((VectorBundleZeroSection.baseObject S).obj.hom ⁻¹ᵁ U)
          (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
        eqToHom (by rw [hobj (VectorBundleZeroSection.baseObject S)]; rfl))
    (he : c ≫ (F.map h.op).hom = a ≫
      Under.homMk (F.obj (op (VectorBundleZeroSection.baseObject S))).obj.hom
        (Category.id_comp _)) :
    (c ≫ eqToHom (hobj Y)).right.hom.app (op U) ≫
      h.hom.left.appLE (Y.obj.hom ⁻¹ᵁ U)
        ((VectorBundleZeroSection.baseObject S).obj.hom ⁻¹ᵁ U)
        (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) =
          a.right.hom.app (op U) := by
  exact transport_augmentation_app (hobj Y)
    (hobj (VectorBundleZeroSection.baseObject S)) (F.map h.op).hom c a U _ hm he

/-- The section of the relative spectrum induced by the conormal augmentation pulls
functions back by that same augmentation, under the canonical counit algebra isomorphism.
Source: Stacks Tag 01LX, contravariant relative Spec, and Tag 0630, conormal algebra.
(blueprint: lem-pur-conormal-zero-section-pullback).

Proof: Let E be the fixed affine-morphism/relative-Spec anti-equivalence. The section is
by definition E.functor.preimage of the counit followed by augmentationToBase. Applying
E.functor cancels preimage by full faithfulness. The sectionwise morphism formula of
affine_morphism_relative_spec identifies the resulting arrow with pullback on sections,
with the object-equality transports at its two ends. Precompose with the inverse counit;
the counit cancels. Postcompose with the base-object transport. Since augmentationToBase
is the augmentation followed by the base object's structural map, the under-category
triangle makes that structural map the identity on O_S. The remaining equality is the
displayed equality. This argument includes empty bases and zero or unit ideals. -/
theorem coneZeroSection_app {V S : Scheme.{u}} (s : S ⟶ V)
    [IsClosedImmersion s] (U : S.Opens) :
    (coneAlgebraIso s).hom.right.hom.app (op U) ≫
      (PurityNormalBundle.zeroSection s).appLE (PurityNormalBundle.projection s ⁻¹ᵁ U) U
        (by rw [← Scheme.Hom.comp_preimage, (PurityNormalBundle.zeroSection_spec s).1]; simp) =
      (ConormalGradedAlgebra.augmentation s).right.hom.app (op U) := by
  let E := VectorBundleZeroSection.antiEquivalence S
  have hobj := relativeSpec_obj S
  have hmap := relativeSpec_map S
  let A := PurityNormalBundle.algebraObject s
  let B := VectorBundleZeroSection.baseObject S
  let Y := (E.inverse.obj A).unop
  let ε : E.functor.obj (E.inverse.obj A) ⟶ E.functor.obj (op B) :=
    (E.counitIso.app A).hom ≫ ObjectProperty.homMk
      (PurityNormalBundle.augmentationToBase s)
  let h : B ⟶ Y := (E.functor.preimage ε).unop
  have hp : E.functor.map h.op = ε := E.functor.map_preimage ε
  have he := fullSubcategory_iso_cancel (E.counitIso.app A)
    (PurityNormalBundle.augmentationToBase s) (E.functor.map h.op) hp
  have h0 := functor_section_app S E.functor
  have h1 := h0 hobj (A := A.obj)
  have h2 := h1 Y
  have h3 := h2 h
  have h4 := h3 (E.counitIso.app A).inv.hom
  have h5 := h4 (ConormalGradedAlgebra.augmentation s) U
  have h6 := h5 (hmap B Y h U)
  have hs := h6 he
  simpa only [coneAlgebraIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    ObjectProperty.ι_map, eqToIso.hom, eqToHom_refl, Category.comp_id,
    PurityNormalBundle.over,
    VectorBundleZeroSection.antiEquivalence, A, B, Y, h, ε, E,
    PurityNormalBundle.zeroSection, PurityNormalBundle.projection,
    VectorBundleZeroSection.baseObject, Over.mk_hom, Scheme.Hom.id_preimage] using hs

end AlgebraicGeometry.Etale.FiniteSmoothPurity
