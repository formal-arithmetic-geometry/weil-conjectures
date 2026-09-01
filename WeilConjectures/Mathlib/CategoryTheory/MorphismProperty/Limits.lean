/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphism properties and binary products in over categories

If `C` has pullbacks, the binary product of `A` and `B` in `Over S` has as underlying object the
fibre product `A.left ×[S] B.left`. Hence, for a morphism `g : B ⟶ B'` in `Over S`, the underlying
morphism of `prod.map (𝟙 A) g` is a base change of `g.left`. We deduce that any morphism property
that is stable under base change is stable under taking the product with the identity of a fixed
object of `Over S`.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (P : MorphismProperty C)
  [P.IsStableUnderBaseChange] {S : C} {A B B' : Over S}

/-- The underlying morphism of `prod.map (𝟙 A) g` is, up to the canonical identification of the
binary product in `Over S` with the fibre product over `S`, the base change of `g.left` along
`pullback.snd A.hom B'.hom`. -/
lemma isPullback_pullbackMap_id (g : B ⟶ B') :
    IsPullback (pullback.snd A.hom B.hom)
      (pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
        (by simp [Over.w])) g.left (pullback.snd A.hom B'.hom) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback A.hom B'.hom).flip
  have : pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
      (by simp [Over.w]) ≫ pullback.fst A.hom B'.hom = pullback.fst A.hom B.hom := by simp
  rw [this, Over.w g]
  exact (IsPullback.of_hasPullback A.hom B.hom).flip

/-- Up to the canonical identification of binary products in `Over S` with fibre products over
`S`, the underlying morphism of `prod.map (𝟙 A) g` is `pullback.map`. -/
lemma prod_map_id_left_comp_prodLeftIsoPullback_hom (g : B ⟶ B') :
    (prod.map (𝟙 A) g).left ≫ (Over.prodLeftIsoPullback A B').hom =
      (Over.prodLeftIsoPullback A B).hom ≫
        pullback.map A.hom B.hom A.hom B'.hom (𝟙 A.left) g.left (𝟙 S) (by simp)
          (by simp [Over.w]) := by
  ext
  · simp [← Over.comp_left]
  · simp [← Over.comp_left]

/-- A morphism property stable under base change is stable under taking the product with the
identity in an over category: if `g : B ⟶ B'` in `Over S` satisfies `P g.left`, then
`P (prod.map (𝟙 A) g).left`. -/
theorem left_prod_map_id (g : B ⟶ B') (hg : P g.left) : P (prod.map (𝟙 A) g).left := by
  rw [← P.cancel_right_of_respectsIso _ (Over.prodLeftIsoPullback A B').hom,
    prod_map_id_left_comp_prodLeftIsoPullback_hom, P.cancel_left_of_respectsIso]
  exact P.of_isPullback (isPullback_pullbackMap_id g) hg

/-- A morphism property stable under base change is stable under taking the product with the
identity in an over category: if `g : B ⟶ B'` in `Over S` satisfies `P g.left`, then
`P (prod.map g (𝟙 A)).left`. -/
theorem left_prod_map_id' (g : B ⟶ B') (hg : P g.left) : P (prod.map g (𝟙 A)).left := by
  have h : prod.map g (𝟙 A) =
      (prod.braiding A B).inv ≫ prod.map (𝟙 A) g ≫ (prod.braiding A B').hom := by
    ext <;> simp
  have : IsIso ((prod.braiding A B).inv.left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (prod.braiding A B).inv))
  have : IsIso ((prod.braiding A B').hom.left) :=
    inferInstanceAs (IsIso ((Over.forget S).map (prod.braiding A B').hom))
  rw [h, Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]
  exact P.left_prod_map_id g hg

end CategoryTheory.MorphismProperty
