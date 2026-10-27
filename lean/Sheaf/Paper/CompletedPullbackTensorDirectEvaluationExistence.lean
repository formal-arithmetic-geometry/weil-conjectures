/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems

/-! Existence part of the sectionwise direct-image/evaluation comparison.

Source: Stacks 03D1 and 0941 (blueprint:
`def-pur-completed-pullback-tensor-comparison`; blueprint:
`lem-pur-completed-pullback-tensor-direct-evaluation-existence`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] AlgebraicGeometry.Scheme.coefficientProEtaleDirectRingMap
  SheafOfModules.pushforwardComp SheafOfModules.pushforwardCongr
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue CategoryTheory.constantSheaf

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open WeilConjectures

namespace WeilConjectures

private def SectionwiseIdentity
    {A D : Type*} [Category* A] [Category* D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {F G : A ⥤ SheafOfModules.{v} R} (e : F ≅ G) : Prop :=
  ∀ (M : A) (U : Dᵒᵖ) (x : (F.obj M).val.obj U),
    HEq ((e.hom.app M).val.app U x) x

private theorem sectionwiseIdentity_trans
    {A D : Type*} [Category* A] [Category* D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {F G H : A ⥤ SheafOfModules.{v} R} (e : F ≅ G) (e' : G ≅ H)
    (he : SectionwiseIdentity e) (he' : SectionwiseIdentity e') :
    SectionwiseIdentity (e ≪≫ e') := by
  intro M U x
  change HEq ((e'.hom.app M).val.app U ((e.hom.app M).val.app U x)) x
  exact (he' M U _).trans (he M U x)

private theorem pushforwardComp_sectionwise
    {C D D' : Type*} [Category* C] [Category* D] [Category* D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {K' : GrothendieckTopology D'} {F : C ⥤ D} {G : D ⥤ D'}
    [F.IsContinuous J K] [G.IsContinuous K K']
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {T : Sheaf K' RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat K K').obj T) :
    SectionwiseIdentity (SheafOfModules.pushforwardComp.{v} φ ψ) ∧
      SectionwiseIdentity (SheafOfModules.pushforwardComp.{v} φ ψ).symm := by
  constructor
  · intro M U x
    exact heq_of_eq (SheafOfModules.pushforwardComp_hom_app_val_app φ ψ M U x)
  · intro M U x
    exact heq_of_eq (SheafOfModules.pushforwardComp_inv_app_val_app φ ψ M U x)

private theorem pushforwardCongr_sectionwise
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R} (h : φ = ψ) :
    SectionwiseIdentity (SheafOfModules.pushforwardCongr.{v} h) := by
  intro M U x
  exact heq_of_eq (SheafOfModules.pushforwardCongr_hom_app_val_app h M U x)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

def completedPullbackTensorDirectEvaluationBase {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
        (coefficientSequenceCommRingSheaf l E X)) :=
  SheafOfModules.pushforward.{u + 1}
    (F := integralComparisonSequenceBaseChange f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight ρ.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- For the canonical coefficient map, the sectionwise identity exists before uniqueness
is imposed. The two functors
evaluate a sequence module at the same pulled-back pro-etale section, and their scalar
actions are induced by the same constant-section map. This is the existence half of the
direct-image/evaluation comparison; uniqueness is proved by sheaf extensionality in the
consumer theorem (blueprint: lem-pur-completed-pullback-tensor-direct-evaluation-existence).
-/
theorem completedPullbackTensorDirectEvaluation_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
        (coefficientSequenceCommRingSheaf l E X)) (n : ℕ)
    (hρ : ρ = integralComparisonSequenceRingMap l E f) :
    ∃ e : completedPullbackTensorDirectEvaluationBase l E f ρ ⋙
        coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((completedPullbackTensorDirectEvaluationBase l E f ρ).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  subst ρ
  let a := eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
  let b := eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let c := (show
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (coefficientSequenceCommRingSheaf l E Y) ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous RingCat
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E X)) from
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  let d := (show
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralCoefficientCommRingSheaf l E Y n) ⟶
      ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat
        (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (integralCoefficientCommRingSheaf l E X n)) from
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  let := Functor.isContinuous_comp (Prod.sectR n Y.ProEt)
    (integralComparisonSequenceBaseChange f) (ProEt.topology Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X))
  let := Functor.isContinuous_comp (proEtaleBaseChange f) (Prod.sectR n X.ProEt)
    (ProEt.topology Y) (ProEt.topology X)
      (coefficientSequenceTopology (ProEt.topology X))
  have h : a ≫ ((Prod.sectR n Y.ProEt).sheafPushforwardContinuous RingCat
      (ProEt.topology Y) (coefficientSequenceTopology (ProEt.topology Y))).map c =
      d ≫ ((proEtaleBaseChange f).sheafPushforwardContinuous RingCat
        (ProEt.topology Y) (ProEt.topology X)).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have ha : a.hom.app U = 𝟙 _ := by
      dsimp only [a]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hb : b.hom.app ((proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
      dsimp only [b]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change a.hom.app U ≫ c.hom.app (op (n, U.unop)) =
      d.hom.app U ≫ b.hom.app ((proEtaleBaseChange f).op.obj U)
    rw [ha, hb]
    change 𝟙 _ ≫ d.hom.app U = d.hom.app U ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  let γ := SheafOfModules.pushforwardCongr
    (F := Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange f)
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X)) h
  let e := SheafOfModules.pushforwardComp a c ≪≫ γ ≪≫
    (SheafOfModules.pushforwardComp d b).symm
  have hγ := pushforwardCongr_sectionwise
    (F := Prod.sectR n Y.ProEt ⋙ integralComparisonSequenceBaseChange f)
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X)) h
  have he := sectionwiseIdentity_trans (SheafOfModules.pushforwardComp a c)
    (γ ≪≫ (SheafOfModules.pushforwardComp d b).symm)
    (pushforwardComp_sectionwise a c).1
    (sectionwiseIdentity_trans γ (SheafOfModules.pushforwardComp d b).symm hγ
      (pushforwardComp_sectionwise d b).2)
  exact ⟨e, fun M U x ↦ he M (op U) x⟩

/-- Sectionwise identity determines the direct-image/evaluation comparison uniquely.
Source: Stacks 03D1 and 0941 (blueprint:
`def-pur-completed-pullback-tensor-comparison`; blueprint:
`lem-pur-completed-pullback-tensor-direct-evaluation-existence`). -/
theorem completedPullbackTensorDirectEvaluation_unique
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
        (coefficientSequenceCommRingSheaf l E X)) (n : ℕ)
    {e e' : completedPullbackTensorDirectEvaluationBase l E f ρ ⋙
        coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))}
    (he : ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
      (x : ((coefficientSequenceEvaluation l E Y n).obj
        ((completedPullbackTensorDirectEvaluationBase l E f ρ).obj M)).val.obj (op U)),
      HEq ((e.hom.app M).val.app (op U) x) x)
    (he' : ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
      (x : ((coefficientSequenceEvaluation l E Y n).obj
        ((completedPullbackTensorDirectEvaluationBase l E f ρ).obj M)).val.obj (op U)),
      HEq ((e'.hom.app M).val.app (op U) x) x) :
    e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  exact eq_of_heq ((he M U.unop x).trans (he' M U.unop x).symm)

end WeilConjectures
