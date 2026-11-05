/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree
public import WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor
public import Mathlib.CategoryTheory.Localization.Prod

/-!
# Left derived quadrifunctors

Migrated from `Mathlib/CategoryTheory/Functor/Derived/LeftDerivedFour.lean`
on the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ H : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
--@[simps!]
def whiskeringLeft₄Equiv {F : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H} {G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ H}
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄} :
    ((((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj F ⟶ G) ≃
      (L₁.prod (L₂.prod (L₃.prod L₄)) ⋙ uncurry₄.obj F ⟶ uncurry₄.obj G) where
  toFun α :=
    { app := fun ⟨X₁, X₂, X₃, X₄⟩ ↦ (((α.app X₁).app X₂).app X₃).app X₄
      naturality := by
        rintro ⟨X₁, X₂, X₃, X₄⟩ ⟨Y₁, Y₂, Y₃, Y₄⟩ ⟨f₁, f₂, f₃, f₄⟩
        have h₁ := congr_app (congr_app (congr_app (α.naturality f₁) X₂) X₃) X₄
        have h₂ := congr_app (congr_app ((α.app Y₁).naturality f₂) X₃) X₄
        have h₃ := congr_app (((α.app Y₁).app Y₂).naturality f₃) X₄
        have h₄ := (((α.app Y₁).app Y₂).app Y₃).naturality f₄
        dsimp [uncurry₄, currying₄, Prod.mkHom] at h₁ h₂ h₃ h₄ ⊢
        simp only [Category.assoc]
        rw [← reassoc_of% h₁, ← reassoc_of% h₂, ← reassoc_of% h₃, h₄] }
  invFun β :=
    { app X₁ :=
      { app X₂ :=
        { app X₃ :=
          { app X₄ := β.app (X₁, X₂, X₃, X₄)
            naturality _ _ f₄ := by
              simpa using β.naturality ((𝟙 X₁, 𝟙 X₂, 𝟙 X₃, f₄) : (_, _, _, _) ⟶ (_, _, _, _)) }
          naturality _ _ f₃ := by
            ext X₄
            simpa using β.naturality ((𝟙 X₁, 𝟙 X₂, f₃, 𝟙 X₄) : (_, _, _, _) ⟶ (_, _, _, _)) }
        naturality _ _ f₂ := by
          ext X₃ X₄
          simpa using β.naturality ((𝟙 X₁, f₂, 𝟙 X₃, 𝟙 X₄) : (_, _, _, _) ⟶ (_, _, _, _)) }
      naturality _ _ f₁ := by
        ext X₂ X₃ X₄
        simpa using β.naturality ((f₁, 𝟙 X₂, 𝟙 X₃, 𝟙 X₄) : (_, _, _, _) ⟶ (_, _, _, _)) }
  left_inv _ := rfl
  right_inv _ := rfl

variable (LF LF' LF'' : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H) (F F' F'' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ H)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄}
  (α : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF ⟶ F)
  (α' : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF' ⟶ F')
  (α'₂ : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF' ⟶ F)
  (α'' : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj LF'' ⟶ F'')
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (W₄ : MorphismProperty C₄) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [L₃.IsLocalization W₃] [L₄.IsLocalization W₄]

@[reducible]
def HasLeftDerivedFunctor₄ :=
  (uncurry₄.obj F).HasLeftDerivedFunctor (W₁.prod (W₂.prod (W₃.prod W₄)))

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
  [W₄.ContainsIdentities]

variable {F F'}

@[reducible]
def IsLeftDerivedFunctor₄ : Prop :=
  (uncurry₄.obj LF).IsLeftDerivedFunctor (whiskeringLeft₄Equiv α) (W₁.prod (W₂.prod (W₃.prod W₄)))

section

variable (F L₁ L₂ L₃ L₄) [HasLeftDerivedFunctor₄ F W₁ W₂ W₃ W₄]

end

section

variable [LF.IsLeftDerivedFunctor₄ α W₁ W₂ W₃ W₄]
  [LF'.IsLeftDerivedFunctor₄ α' W₁ W₂ W₃ W₄]
  [LF''.IsLeftDerivedFunctor₄ α'' W₁ W₂ W₃ W₄]
  (G : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H)
  (β : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).obj G ⟶ F)

include W₁ W₂ W₃ W₄ in
lemma leftDerived₄_ext (G : D₁ ⥤ D₂ ⥤ D₃ ⥤ D₄ ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).map γ₁ ≫ α =
      (((((whiskeringLeft₄ H).obj L₁).obj L₂).obj L₃).obj L₄).map γ₂ ≫ α) : γ₁ = γ₂ := by
  apply uncurry₄.map_injective
  apply leftDerived_ext (α := (whiskeringLeft₄Equiv α)) (W := W₁.prod (W₂.prod (W₃.prod W₄)))
  ext ⟨X₁, X₂, X₃, X₄⟩
  exact congr_app (congr_app (congr_app (congr_app hγ X₁) X₂) X₃) X₄

end

end Functor

end CategoryTheory
