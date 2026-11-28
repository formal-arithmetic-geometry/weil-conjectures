/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Evaluation

/-!
# Towers in a Grothendieck abelian category

`CategoryTheory.isGrothendieckAbelian_tower`: the category `ℕᵒᵖ ⥤ A` of towers in a
Grothendieck abelian category `A` is Grothendieck abelian. The index category `ℕᵒᵖ` lives in
`Type 0`, so this is not a special case of the statement for functor categories indexed by a
category in the universe of the morphisms of `A`.
-/

@[expose] public section

universe a v w

open CategoryTheory Limits

namespace CategoryTheory

/-- Strict towers in a Grothendieck abelian category form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_tower (A : Type a) [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{w, w} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{w, w} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

end CategoryTheory
