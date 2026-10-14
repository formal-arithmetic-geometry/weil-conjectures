/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Limits of pointwise pullback diagrams

Source: the universal property of limits; Stacks Project, Tag 01ZM.
-/

@[expose] public section

universe u v w w'

open CategoryTheory Limits

namespace CategoryTheory.Limits

/-- Taking fibre products over a fixed object commutes with a nonempty limit.
 Construct the two maps to the limiting object from the projections of a cone. Their
 composites to the fixed base agree at any chosen index, so they lift to its double fibre
 product. Factorization and uniqueness are checked on the two projections and then at every
 index. This is the universal-property proof that limits commute with limits.

Source: universal properties of limits and fibre products (Stacks Project, Tag 002L).
(blueprint: lem-pd-pointwise-pullback-limit) -/
noncomputable def isLimit_pointwisePullback
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {I : Type w} [Category.{w'} I] [Nonempty I]
    (D₁ D₂ : I ⥤ C) {S : C}
    (t₁ : D₁ ⟶ (Functor.const I).obj S) (t₂ : D₂ ⟶ (Functor.const I).obj S)
    (c₁ : Cone D₁) (c₂ : Cone D₂) (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂)
    (f₁ : c₁.pt ⟶ S) (f₂ : c₂.pt ⟶ S)
    (hf₁ : ∀ i, c₁.π.app i ≫ t₁.app i = f₁)
    (hf₂ : ∀ i, c₂.π.app i ≫ t₂.app i = f₂) :
    let E : I ⥤ C :=
      { obj i := pullback (t₁.app i) (t₂.app i)
        map {i j} g := pullback.map _ _ _ _ (D₁.map g) (D₂.map g) (𝟙 S)
          (by simp only [t₁.naturality, Functor.const_obj_map])
          (by simp only [t₂.naturality, Functor.const_obj_map])
        map_id i := by apply pullback.hom_ext <;> simp
        map_comp g h := by apply pullback.hom_ext <;> simp [Category.assoc] }
    let e : Cone E :=
      { pt := pullback f₁ f₂
        π :=
          { app i := pullback.map _ _ _ _ (c₁.π.app i) (c₂.π.app i) (𝟙 S)
              (by simp [hf₁]) (by simp [hf₂])
            naturality i j g := by apply pullback.hom_ext <;> simp [E, Category.assoc] } }
    IsLimit e := by
  dsimp only
  let E : I ⥤ C :=
    { obj i := pullback (t₁.app i) (t₂.app i)
      map {i j} g := pullback.map _ _ _ _ (D₁.map g) (D₂.map g) (𝟙 S)
        (by simp only [t₁.naturality, Functor.const_obj_map])
        (by simp only [t₂.naturality, Functor.const_obj_map])
      map_id i := by apply pullback.hom_ext <;> simp
      map_comp g h := by apply pullback.hom_ext <;> simp [Category.assoc] }
  let a : E ⟶ D₁ :=
    { app i := pullback.fst _ _
      naturality i j g := by simp [E] }
  let b : E ⟶ D₂ :=
    { app i := pullback.snd _ _
      naturality i j g := by simp [E] }
  let l₁ (s : Cone E) := hc₁.lift ((Cone.postcompose a).obj s)
  let l₂ (s : Cone E) := hc₂.lift ((Cone.postcompose b).obj s)
  have hl (s : Cone E) : l₁ s ≫ f₁ = l₂ s ≫ f₂ := by
    let i := Classical.arbitrary I
    rw [← hf₁ i, ← hf₂ i, ← Category.assoc, ← Category.assoc]
    simp only [l₁, l₂, hc₁.fac, hc₂.fac, Cone.postcompose_obj_π, NatTrans.comp_app]
    simp [a, b, Category.assoc, pullback.condition]
  refine
    { lift := fun s ↦ pullback.lift (l₁ s) (l₂ s) (hl s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply pullback.hom_ext <;> simp [l₁, l₂, a, b, Category.assoc]
  · intro s m hm
    apply pullback.hom_ext
    · apply hc₁.hom_ext
      intro i
      have h := congrArg (fun z ↦ z ≫ pullback.fst (t₁.app i) (t₂.app i)) (hm i)
      simpa [l₁, a, Category.assoc] using h
    · apply hc₂.hom_ext
      intro i
      have h := congrArg (fun z ↦ z ≫ pullback.snd (t₁.app i) (t₂.app i)) (hm i)
      simpa [l₂, b, Category.assoc] using h

end CategoryTheory.Limits
