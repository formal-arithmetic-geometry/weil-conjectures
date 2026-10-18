/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Morphisms between finite coproducts of connected objects

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0, item (8) and proof
(blueprint: lem-galois-coproduct-morphism-components).
-/

@[expose] public section

universe u v w x y

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN0, item (8)
(blueprint: lem-galois-coproduct-morphism-components). A morphism between finite
coproducts of connected objects is induced by a map of indices and component maps.

Proof: Exactness of `F` sends both coproducts to disjoint unions and an initial
object to the empty set. A connected object has a nonempty fibre, since `F`
reflects isomorphisms. Each target coprojection is mono because `F` sends it to
an injection. For each pair of indices, pull back the target coprojection along
the source component map. Its projection to the connected source component is
mono, so its domain is initial or the projection is an isomorphism. Choose a
point in the source fibre; its image lies in a unique target summand. Exactness
on pullbacks shows that the corresponding pullback has a point, hence is not
initial, so its projection is an isomorphism. Compose the other pullback
projection with its inverse to obtain the component map. The pullback square
gives the displayed equality, and coproduct uniqueness identifies the induced
map with the original morphism. For an empty source index, use the empty map. -/
theorem morphism_coproduct_connected_components
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F)
    {α : Type x} {β : Type y} [Finite α] [Finite β]
    {X Y : C} {Xᵢ : α → C} {Yⱼ : β → C}
    {ι : (i : α) → Xᵢ i ⟶ X} {κ : (j : β) → Yⱼ j ⟶ Y}
    (hX : IsColimit (Cofan.mk X ι))
    (hY : IsColimit (Cofan.mk Y κ))
    (hXconn : ∀ i, IsConnected (Xᵢ i))
    (hYconn : ∀ j, IsConnected (Yⱼ j))
    (φ : X ⟶ Y) :
    ∃ (a : α → β) (φᵢ : (i : α) → Xᵢ i ⟶ Yⱼ (a i)),
      ∀ i, ι i ≫ φ = φᵢ i ≫ κ (a i) := by
  classical
  have _ := hX
  have _ := hYconn
  have : HasFiniteLimits C := hG.hasFiniteLimits
  have : HasFiniteColimits C := hG.hasFiniteColimits
  have : PreservesFiniteLimits F := hG.preservesFiniteLimits
  have : PreservesFiniteColimits F := hG.preservesFiniteColimits
  have : F.ReflectsIsomorphisms := hG.reflectsIsomorphisms
  have : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape (Discrete PEmpty) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have initial_iff (Z : C) : Nonempty (IsInitial Z) ↔ IsEmpty (F.obj Z) := by
    rw [(IsInitial.isInitialIffObj F Z).nonempty_congr]
    exact Types.initial_iff_empty (F.obj Z)
  have hFY := isColimitCofanMkObjOfIsColimit F Yⱼ κ hY
  have hκ (j : β) : Mono (κ j) := by
    have : Mono (F.map (κ j)) :=
      (mono_iff_injective _).2 (Cofan.inj_injective_of_isColimit hFY j)
    exact reflects_mono_of_reflectsLimit F (κ j)
  have components (i : α) : ∃ (j : β) (f : Xᵢ i ⟶ Yⱼ j),
      ι i ≫ φ = f ≫ κ j := by
    have : IsConnected (Xᵢ i) := hXconn i
    have hne : Nonempty (F.obj (Xᵢ i)) := by
      by_contra h
      obtain ⟨hi⟩ := (initial_iff (Xᵢ i)).2 (not_nonempty_iff.mp h)
      exact IsConnected.notInitial hi
    obtain ⟨s⟩ := hne
    obtain ⟨j, t, ht⟩ := Cofan.inj_jointly_surjective_of_isColimit hFY
      (F.map (ι i ≫ φ) s)
    have : Mono (κ j) := hκ j
    let f := ι i ≫ φ
    have hpb := (IsPullback.of_hasPullback f (κ j)).map F
    obtain ⟨e, _, _⟩ := Types.exists_of_isPullback hpb s t ht.symm
    have hnot : IsInitial (pullback f (κ j)) → False := by
      intro hi
      exact ((initial_iff _).1 ⟨hi⟩).false e
    have : IsIso (pullback.fst f (κ j)) :=
      IsConnected.noTrivialComponent _ _ hnot
    refine ⟨j, inv (pullback.fst f (κ j)) ≫ pullback.snd f (κ j), ?_⟩
    change f = _
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  choose a f hf using components
  exact ⟨a, f, hf⟩

end CategoryTheory
