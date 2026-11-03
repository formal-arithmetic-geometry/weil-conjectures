/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalHomComparisonNaturality
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo

/-! # The covariant shift square for the external Hom comparison

Source: sk-def-sf-kv-maps (iii), the evaluation transpose in the proof of
lem-sf-kv-exact-comparisons, Step 8.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory.MonoidalClosed

variable {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂]
  [HasShift C ℤ] [HasShift D₁ ℤ] [Preadditive C] [Preadditive D₁]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive]
  [(curriedTensor C).CommShift₂Int] [(curriedTensor D₁).CommShift₂Int]
  (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]
  [F₁.CommShift ℤ]

/-- A shift-compatible tensorator and the signed interchange square give compatibility
of the specified evaluation transpose in its first target input. The proof pastes the
interchange, tensorator and evaluation squares and takes their adjunction mate.
Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-covariant-shifts). -/
theorem externalIhomTargetLeft_commShift (E₁ : D₁) (E₂ L₂ : D₂)
    [NatTrans.CommShift (F₁ := F₁ ⋙ tensorLeft (F₁.obj E₁))
      (F₂ := tensorLeft E₁ ⋙ F₁) ((Functor.LaxMonoidal.μNatTrans F₁).app E₁) ℤ]
    (μ : tensorRight (F₂.obj ((ihom E₂).obj L₂)) ⋙
        tensorLeft (F₁.obj E₁ ⊗ F₂.obj E₂) ⟶
      tensorLeft (F₁.obj E₁) ⋙
        tensorRight (F₂.obj E₂ ⊗ F₂.obj ((ihom E₂).obj L₂)))
    [NatTrans.CommShift μ ℤ]
    (hμ : ∀ U, μ.app U = tensorμ (F₁.obj E₁) (F₂.obj E₂) U
      (F₂.obj ((ihom E₂).obj L₂))) :
    letI : (ihom E₁).CommShift ℤ := (ihom.adjunction E₁).rightAdjointCommShift ℤ
    letI : (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
      (ihom.adjunction _).rightAdjointCommShift ℤ
    NatTrans.CommShift (externalIhomTargetLeft F₁ F₂ E₁ E₂ L₂) ℤ := by
  let : (ihom E₁).CommShift ℤ := (ihom.adjunction E₁).rightAdjointCommShift ℤ
  let : (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
    (ihom.adjunction _).rightAdjointCommShift ℤ
  have : (ihom.adjunction E₁).CommShift ℤ :=
    (ihom.adjunction E₁).commShift_of_leftAdjoint ℤ
  have : (ihom.adjunction (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
    (ihom.adjunction _).commShift_of_leftAdjoint ℤ
  let m : F₁ ⋙ tensorLeft (F₁.obj E₁) ⟶ tensorLeft E₁ ⋙ F₁ :=
    (Functor.LaxMonoidal.μNatTrans F₁).app E₁
  have : NatTrans.CommShift m ℤ := inferInstance
  let ε : (ihom E₁ ⋙ F₁) ⋙ tensorLeft (F₁.obj E₁) ⟶ F₁ :=
    (Functor.associator (ihom E₁) F₁ (tensorLeft (F₁.obj E₁))).hom ≫
      Functor.whiskerLeft (ihom E₁) m ≫
      (Functor.associator (ihom E₁) (tensorLeft E₁) F₁).inv ≫
      Functor.whiskerRight (ihom.ev E₁) F₁ ≫ (Functor.leftUnitor F₁).hom
  have : NatTrans.CommShift ε ℤ := by dsimp only [ε, ihom.ev]; infer_instance
  let e₂ := Functor.LaxMonoidal.μ F₂ E₂ ((ihom E₂).obj L₂) ≫
    F₂.map ((ihom.ev E₂).app L₂)
  let τ : (ihom E₁ ⋙ F₁ ⋙ tensorRight (F₂.obj ((ihom E₂).obj L₂))) ⋙
      tensorLeft (F₁.obj E₁ ⊗ F₂.obj E₂) ⟶ F₁ ⋙ tensorRight (F₂.obj L₂) :=
    Functor.whiskerRight (Functor.associator (ihom E₁) F₁
        (tensorRight (F₂.obj ((ihom E₂).obj L₂)))).inv (tensorLeft _) ≫
      (Functor.associator (ihom E₁ ⋙ F₁)
        (tensorRight (F₂.obj ((ihom E₂).obj L₂))) (tensorLeft _)).hom ≫
      Functor.whiskerLeft (ihom E₁ ⋙ F₁) μ ≫
      (Functor.associator (ihom E₁ ⋙ F₁) (tensorLeft (F₁.obj E₁))
        (tensorRight (F₂.obj E₂ ⊗ F₂.obj ((ihom E₂).obj L₂)))).inv ≫
      Functor.whiskerRight ε
        (tensorRight (F₂.obj E₂ ⊗ F₂.obj ((ihom E₂).obj L₂))) ≫
      Functor.whiskerLeft F₁ ((curriedTensor C).flip.map e₂)
  have : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
  let σ : (ihom E₁ ⋙ F₁ ⋙
        tensorRight (F₂.obj ((ihom E₂).obj L₂))) ⟶
      (F₁ ⋙ tensorRight (F₂.obj L₂)) ⋙ ihom (F₁.obj E₁ ⊗ F₂.obj E₂) :=
    externalIhomTargetLeft F₁ F₂ E₁ E₂ L₂
  have hσ : NatTrans.CommShift σ ℤ := by
    apply NatTrans.CommShift.of_homEquiv (ihom.adjunction _) τ σ
    intro L₁
    change curry _ = curry _
    congr 1
    simp only [τ, ε, m, e₂, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, hμ, Functor.map_comp, Category.assoc,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.map_id, Category.id_comp,
      Functor.flip_map_app]
    erw [Category.id_comp]
    simp only [tensorRight, tensorLeft, Functor.flip_obj_map, curriedTensor_map_app,
      curriedTensor_obj_map, Functor.LaxMonoidal.μNatTrans_app_app,
      tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    erw [id_whiskerRight, Category.id_comp]
    rfl
  have he : externalIhomTargetLeft F₁ F₂ E₁ E₂ L₂ = σ ≫
      (Functor.associator F₁ (tensorRight (F₂.obj L₂))
        (ihom (F₁.obj E₁ ⊗ F₂.obj E₂))).hom := by
    ext L₁
    simp only [NatTrans.comp_app, Functor.associator_hom_app, σ, Category.comp_id]
  rw [he]
  infer_instance

variable [HasShift D₂ ℤ] [Preadditive D₂]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [(curriedTensor D₂).CommShift₂Int]
  [F₂.CommShift ℤ]

omit [HasShift D₁ ℤ] [Preadditive D₁]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [(curriedTensor D₁).CommShift₂Int]
  [F₁.CommShift ℤ] in
/-- The same evaluation transpose commutes with the prescribed shifts in the second
target. The pasted square first evaluates its varying second factor and then its
fixed first factor. Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-covariant-shifts). -/
theorem externalIhomTargetRight_commShift (E₁ L₁ : D₁) (E₂ : D₂)
    [NatTrans.CommShift (F₁ := F₂ ⋙ tensorLeft (F₂.obj E₂))
      (F₂ := tensorLeft E₂ ⋙ F₂) ((Functor.LaxMonoidal.μNatTrans F₂).app E₂) ℤ]
    (μ : tensorLeft (F₁.obj ((ihom E₁).obj L₁)) ⋙
        tensorLeft (F₁.obj E₁ ⊗ F₂.obj E₂) ⟶
      tensorLeft (F₂.obj E₂) ⋙
        tensorLeft (F₁.obj E₁ ⊗ F₁.obj ((ihom E₁).obj L₁)))
    [NatTrans.CommShift μ ℤ]
    (hμ : ∀ V, μ.app V = tensorμ (F₁.obj E₁) (F₂.obj E₂)
      (F₁.obj ((ihom E₁).obj L₁)) V) :
    letI : (ihom E₂).CommShift ℤ := (ihom.adjunction E₂).rightAdjointCommShift ℤ
    letI : (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
      (ihom.adjunction _).rightAdjointCommShift ℤ
    NatTrans.CommShift (externalIhomTargetRight F₁ F₂ E₁ L₁ E₂) ℤ := by
  let : (ihom E₂).CommShift ℤ := (ihom.adjunction E₂).rightAdjointCommShift ℤ
  let : (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
    (ihom.adjunction _).rightAdjointCommShift ℤ
  have : (ihom.adjunction E₂).CommShift ℤ :=
    (ihom.adjunction E₂).commShift_of_leftAdjoint ℤ
  have : (ihom.adjunction (F₁.obj E₁ ⊗ F₂.obj E₂)).CommShift ℤ :=
    (ihom.adjunction _).commShift_of_leftAdjoint ℤ
  let m : F₂ ⋙ tensorLeft (F₂.obj E₂) ⟶ tensorLeft E₂ ⋙ F₂ :=
    (Functor.LaxMonoidal.μNatTrans F₂).app E₂
  have : NatTrans.CommShift m ℤ := inferInstance
  let ε : (ihom E₂ ⋙ F₂) ⋙ tensorLeft (F₂.obj E₂) ⟶ F₂ :=
    (Functor.associator (ihom E₂) F₂ (tensorLeft (F₂.obj E₂))).hom ≫
      Functor.whiskerLeft (ihom E₂) m ≫
      (Functor.associator (ihom E₂) (tensorLeft E₂) F₂).inv ≫
      Functor.whiskerRight (ihom.ev E₂) F₂ ≫ (Functor.leftUnitor F₂).hom
  have : NatTrans.CommShift ε ℤ := by dsimp only [ε, ihom.ev]; infer_instance
  let e₁ := Functor.LaxMonoidal.μ F₁ E₁ ((ihom E₁).obj L₁) ≫
    F₁.map ((ihom.ev E₁).app L₁)
  let τ : (ihom E₂ ⋙ F₂ ⋙ tensorLeft (F₁.obj ((ihom E₁).obj L₁))) ⋙
      tensorLeft (F₁.obj E₁ ⊗ F₂.obj E₂) ⟶ F₂ ⋙ tensorLeft (F₁.obj L₁) :=
    Functor.whiskerRight (Functor.associator (ihom E₂) F₂
        (tensorLeft (F₁.obj ((ihom E₁).obj L₁)))).inv (tensorLeft _) ≫
      (Functor.associator (ihom E₂ ⋙ F₂)
        (tensorLeft (F₁.obj ((ihom E₁).obj L₁))) (tensorLeft _)).hom ≫
      Functor.whiskerLeft (ihom E₂ ⋙ F₂) μ ≫
      (Functor.associator (ihom E₂ ⋙ F₂) (tensorLeft (F₂.obj E₂))
        (tensorLeft (F₁.obj E₁ ⊗ F₁.obj ((ihom E₁).obj L₁)))).inv ≫
      Functor.whiskerRight ε
        (tensorLeft (F₁.obj E₁ ⊗ F₁.obj ((ihom E₁).obj L₁))) ≫
      Functor.whiskerLeft F₂ ((curriedTensor C).map e₁)
  have : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
  let σ : (ihom E₂ ⋙ F₂ ⋙
        tensorLeft (F₁.obj ((ihom E₁).obj L₁))) ⟶
      (F₂ ⋙ tensorLeft (F₁.obj L₁)) ⋙ ihom (F₁.obj E₁ ⊗ F₂.obj E₂) :=
    externalIhomTargetRight F₁ F₂ E₁ L₁ E₂
  have hσ : NatTrans.CommShift σ ℤ := by
    apply NatTrans.CommShift.of_homEquiv (ihom.adjunction _) τ σ
    intro L₂
    change curry _ = curry _
    congr 1
    simp only [τ, ε, m, e₁, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, hμ, Functor.map_comp, Category.assoc,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.map_id, Category.id_comp, curriedTensor_map_app]
    erw [Category.id_comp]
    simp only [tensorLeft, curriedTensor_obj_map, Functor.LaxMonoidal.μNatTrans_app_app,
      tensorHom_def', comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    erw [whiskerLeft_id, Category.id_comp]
    rfl
  have he : externalIhomTargetRight F₁ F₂ E₁ L₁ E₂ = σ ≫
      (Functor.associator F₂ (tensorLeft (F₁.obj L₁))
        (ihom (F₁.obj E₁ ⊗ F₂.obj E₂))).hom := by
    ext L₂
    simp only [NatTrans.comp_app, Functor.associator_hom_app, σ, Category.comp_id]
  rw [he]
  infer_instance

end CategoryTheory.MonoidalClosed
