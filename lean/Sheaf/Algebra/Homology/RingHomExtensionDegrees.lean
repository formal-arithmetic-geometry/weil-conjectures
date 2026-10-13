/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Degree maps for normalized scalar extension of Hom complexes

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-degrees)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open scoped ChangeOfRings

namespace CategoryTheory


private noncomputable def pointLift {A : Type u} [CommRing A]
    (M N : RingSiteModules A)
    (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ⟶ N where
  val :=
    { app := fun U ↦ by
        rcases U with ⟨⟨⟨⟩⟩⟩
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        rcases U with ⟨⟨⟨⟩⟩⟩
        rcases V with ⟨⟨⟨⟩⟩⟩
        have hi : i = 𝟙 (op (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1})) :=
          Subsingleton.elim _ _
        subst i
        ext x
        simp }

private noncomputable def pointHomEquiv {A : Type u} [CommRing A]
    (M N : RingSiteModules A) :
    (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
      (op ⟨PUnit.unit⟩) ≃ₗ[A]
        (M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) where
  toFun f := (f.app (op (Over.mk (𝟙 _)))).hom
  invFun f :=
    { app := fun W ↦ by
        have hW : W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst W
        exact ModuleCat.ofHom f
      naturality := by
        intro U V i
        have hU : U = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases U with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst U
        have hV : V = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
          rcases V with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
          rfl
        subst V
        have hi : i = 𝟙 _ := by
          apply Quiver.Hom.unop_inj
          ext
          apply Subsingleton.elim
        subst i
        ext x
        simp
        rfl }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro W
    have hW : W = op (Over.mk (𝟙 (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))) := by
      rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
      rfl
    subst W
    rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' a f := by
    ext x
    rfl

private noncomputable def pointExtensionEquiv
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) :
    letI := φ.toAlgebra
    B ⊗[A] M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[B]
      (F.obj M).val.obj (op ⟨PUnit.unit⟩) := by
  letI := φ.toAlgebra
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M
  let η := toSheafify ⊥ T.presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  let α := (eqToHom (hF M).symm).val.app (op ⟨PUnit.unit⟩)
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ _).map (eqToHom (hF M).symm))
    infer_instance
  let e : B ⊗[A] M.val.obj (op ⟨PUnit.unit⟩) →ₗ[B]
      (SheafOfModules.changeOfRings (ringSiteMap φ) M).val.obj (op ⟨PUnit.unit⟩) :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app T).app
      (op ⟨PUnit.unit⟩) |>.hom
  exact (LinearEquiv.ofBijective e
    (ConcreteCategory.bijective_of_isIso (η.app (op ⟨PUnit.unit⟩)))).trans
    (LinearEquiv.ofBijective α.hom (ConcreteCategory.bijective_of_isIso α))

set_option backward.isDefEq.respectTransparency false in
private theorem ringExtension_map_pure
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    {M N : RingSiteModules A} (a : M ⟶ N)
    (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b : B) (x : M.val.obj U) :
    (F.map a).val.app U (ringExtensionPure φ F h M U b x) =
      ringExtensionPure φ F h N U b (a.val.app U x) := by
  let : Module A B := Module.compHom B φ
  have hmap : eqToHom (h M).symm ≫ F.map a =
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M a ≫ eqToHom (h N).symm := by
    rw [hm]
    simp
  change ((eqToHom (h M).symm ≫ F.map a).val.app U)
    ((toSheafify ⊥
      (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
        (b ⊗ₜ[A, φ] x)) = _
  rw [hmap]
  change (eqToHom (h N).symm).val.app U
    ((SheafOfModules.changeOfRingsHom (ringSiteMap φ) M a).val.app U
      ((toSheafify ⊥
        (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf).app U
          (b ⊗ₜ[A, φ] x))) = _
  apply congrArg ((eqToHom (h N).symm).val.app U)
  let a' : SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (ringSiteMap φ) N :=
    { app := fun U ↦ (ModuleCat.extendScalars ((ringSiteMap φ).hom.app U).hom).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (ringSiteMap φ) M a }
  let α := (PresheafOfModules.toPresheaf _).map a'
  have hn := congr_app (toSheafify_naturality (J := ⊥) α) U
  let : Module A B := Module.compHom B φ
  have hv := congrArg (fun f ↦ f (b ⊗ₜ[A] x)) hn
  exact hv.symm

private theorem internalHom_extension_exists
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M N : RingSiteModules A) :
    ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B) (F.obj M) (F.obj N),
      ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj U)
        (x : M.val.obj U),
        ((g.val.app U (ringExtensionPure φ F h _ U b f)).app
          (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F h M U c x) =
        ringExtensionPure φ F h N U (b * c) ((f.app (op (Over.mk (𝟙 U.unop)))) x) := by
  let := φ.toAlgebra
  let M₀ := M.val.obj (op ⟨PUnit.unit⟩)
  let N₀ := N.val.obj (op ⟨PUnit.unit⟩)
  let t := IsBaseChange.linearMapRightBaseChangeHom B M₀ (TensorProduct.mk A B N₀ 1)
  let k := (LinearMap.liftBaseChangeEquiv B).toLinearMap.comp t
  have hk (b c : B) (f : M₀ →ₗ[A] N₀) (x : M₀) :
      k (b ⊗ₜ[A] f) (c ⊗ₜ[A] x) = (b * c) ⊗ₜ[A] f x := by
    simp [k, t, IsBaseChange.linearMapRightBaseChangeHom, TensorProduct.smul_tmul',
      smul_eq_mul]
  let H := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N
  let HB := SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B)
    (F.obj M) (F.obj N)
  let eM := pointExtensionEquiv φ F h M
  let eN := pointExtensionEquiv φ F h N
  let eH := pointExtensionEquiv φ F h H
  let eA := pointHomEquiv M N
  let eB := pointHomEquiv (F.obj M) (F.obj N)
  let eS := eH.symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl B B) eA)
  let eT := (LinearEquiv.arrowCongr eM eN).trans eB.symm
  let l := eT.toLinearMap.comp (k.comp eS.toLinearMap)
  refine ⟨pointLift (F.obj H) HB l, ?_⟩
  intro U b c f x
  rcases U with ⟨⟨⟨⟩⟩⟩
  change (eB (l (eH (b ⊗ₜ[A] f)))) (eM (c ⊗ₜ[A] x)) = eN ((b * c) ⊗ₜ[A] _)
  change eN (k ((AlgebraTensorModule.congr (LinearEquiv.refl B B) eA)
    (eH.symm (eH (b ⊗ₜ[A] f)))) (eM.symm (eM (c ⊗ₜ[A] x)))) = _
  rw [eH.symm_apply_apply, eM.symm_apply_apply, AlgebraTensorModule.congr_tmul]
  exact congrArg eN (hk b c (eA f) x)

/-- Scalar extension of the shared Hom complex admits a normalized map in each degree.
This asserts no chain-map identity and does not use boundedness or flatness.

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-degrees).

Proof: evaluation at the unique object identifies internal Hom with ordinary module Hom
and extension with B tensor over A; the bottom-topology sheafification unit is invertible.
The ordinary tensor-Hom map sends b tensor f to the map c tensor x -> bc tensor f(x).
Transport it through these identifications. For each product coordinate, compose the
extended source projection with this internal-Hom comparison. The specified map equality
for F and naturality of the sheafification unit give the pure-tensor formula for the
extended projection. Lift the coordinate maps through the target limiting fan chosen
by homComplex_exists. Its factorization equations give the displayed formula. Neither
preservation of infinite products nor finiteness of either complex is required. -/
theorem ringHomExtension_degrees_exists
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    ∃ t : F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n,
      ∀ (p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
        (x : (P.X p).val.obj U),
        ringHomEvaluate ((ringExtensionComplex F hF).obj P)
          ((ringExtensionComplex F hF).obj Q) n p U
          (t.val.app U (ringExtensionPure φ F h _ U b f))
          (ringExtensionPure φ F h (P.X p) U c x) =
        ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
          (ringHomEvaluate P Q n p U f x) := by
  classical
  let : F.Additive := hF
  let FP := (ringExtensionComplex F hF).obj P
  let FQ := (ringExtensionComplex F hF).obj Q
  obtain ⟨hB⟩ :=
    (homComplex_exists (R := CochainComplex.onePointRingSheaf B)).choose_spec.choose_spec.1
      FP FQ n
  choose g hg using fun (p : ℤ) ↦ internalHom_extension_exists φ F h (P.X p) (Q.X (p + n))
  let t : F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf B) FP FQ).X n :=
    Fan.IsLimit.lift hB (fun p ↦ F.map (ringHomComplexProjection P Q n p) ≫ g p)
  have ht (p : ℤ) : t ≫ ringHomComplexProjection FP FQ n p =
      F.map (ringHomComplexProjection P Q n p) ≫ g p := Fan.IsLimit.fac hB _ p
  refine ⟨t, ?_⟩
  intro p U b c f x
  change (((t ≫ ringHomComplexProjection FP FQ n p).val.app U
    (ringExtensionPure φ F h _ U b f)).app (op (Over.mk (𝟙 U.unop))))
      (ringExtensionPure φ F h (P.X p) U c x) = _
  rw [ht]
  change (((g p).val.app U
    ((F.map (ringHomComplexProjection P Q n p)).val.app U
      (ringExtensionPure φ F h _ U b f))).app (op (Over.mk (𝟙 U.unop))))
      (ringExtensionPure φ F h (P.X p) U c x) = _
  rw [ringExtension_map_pure φ F h hm, hg]
  rfl

end CategoryTheory
