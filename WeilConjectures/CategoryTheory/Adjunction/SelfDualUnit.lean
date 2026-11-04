/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Self-dual functors whose unit satisfies the triangle identity

Let `G : Cᵒᵖ ⥤ C` be a contravariant functor and `η : 𝟭 ⟶ G.rightOp ⋙ G` a natural transformation,
`η_A : A ⟶ G G A`, satisfying the triangle identity `G(η_N) ∘ η_{G N} = 𝟙` for every `N`
(`CategoryTheory.Functor.IsSelfDualUnit`). This is the situation of a duality functor
`D = Hom(-, ω)` with its double-dual map. Then `G.rightOp ⊣ G`, with unit `η` and counit `η.op`.
Through the adjunction bijection, `f ↦ G f : (T ⟶ A) → (G A ⟶ G T)` becomes
`f ↦ f ≫ η_A` (`CategoryTheory.Functor.IsSelfDualUnit.bijective_map_op_iff`).

## Main results

- `CategoryTheory.Functor.IsSelfDualUnit.isIso_app_of_bijective`: if `f ↦ G f` is bijective on
  `A ⟶ A` and on `G G A ⟶ A`, then `η_A` is an isomorphism. This is the general form of
  `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_bijective`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite

variable {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ C)

/-- The triangle identity `G(η_N) ∘ η_{G N} = 𝟙` for a natural transformation
`η : 𝟭 ⟶ G.rightOp ⋙ G`. -/
def IsSelfDualUnit (η : 𝟭 C ⟶ G.rightOp ⋙ G) : Prop :=
  ∀ N : C, η.app (G.obj (op N)) ≫ G.map (η.app N).op = 𝟙 _

variable {G} in
/-- The triangle identity at `N` follows from the triangle identity at an isomorphic `N'`. -/
lemma app_comp_map_app_op_of_iso {η : 𝟭 C ⟶ G.rightOp ⋙ G} {N N' : C} (e : N ≅ N')
    (h : η.app (G.obj (op N')) ≫ G.map (η.app N').op = 𝟙 _) :
    η.app (G.obj (op N)) ≫ G.map (η.app N).op = 𝟙 _ := by
  have h₁ := η.naturality (G.map e.hom.op)
  have h₂ := η.naturality e.hom
  dsimp at h₁ h₂
  have key : G.map e.hom.op ≫ η.app (G.obj (op N)) ≫ G.map (η.app N).op =
      (η.app (G.obj (op N')) ≫ G.map (η.app N').op) ≫ G.map e.hom.op := by
    rw [reassoc_of% h₁, ← G.map_comp, ← op_comp, ← h₂, op_comp, G.map_comp, Category.assoc]
  rw [h, Category.id_comp] at key
  rw [← cancel_epi (G.map e.hom.op), key]
  exact (Category.comp_id _).symm

namespace IsSelfDualUnit

variable {G} {η : 𝟭 C ⟶ G.rightOp ⋙ G} (hη : G.IsSelfDualUnit η)
include hη

/-- The map `f ↦ G f : (T ⟶ A) → (G A ⟶ G T)` is bijective if and only if
`g ↦ g ≫ η_A : (T ⟶ A) → (T ⟶ G G A)` is: the two maps differ by the bijection
`(G A ⟶ G T) ≃ (T ⟶ G G A)`, `h ↦ η_T ≫ G h`, of the adjunction `G.rightOp ⊣ G`. -/
lemma bijective_map_op_iff (T A : C) :
    Function.Bijective (fun f : T ⟶ A ↦ G.map f.op) ↔
      Function.Bijective (fun f : T ⟶ A ↦ f ≫ η.app A) := by
  let φ : (G.obj (op A) ⟶ G.obj (op T)) → (T ⟶ G.obj (op (G.obj (op A)))) :=
    fun h ↦ η.app T ≫ G.map h.op
  have hφ : Function.Bijective φ := by
    refine ⟨fun h h' hh ↦ ?_, fun g ↦ ⟨η.app (G.obj (op A)) ≫ G.map g.op, ?_⟩⟩
    · have key (h : G.obj (op A) ⟶ G.obj (op T)) :
          η.app (G.obj (op A)) ≫ G.map (φ h).op = h := by
        have := η.naturality h
        dsimp at this
        simp only [φ, op_comp, G.map_comp, ← Category.assoc, ← this]
        rw [Category.assoc, hη]
        exact Category.comp_id _
      rw [← key h, ← key h', hh]
    · have := η.naturality g
      dsimp at this
      simp only [φ, op_comp, G.map_comp, ← Category.assoc, ← this]
      rw [Category.assoc, hη]
      exact Category.comp_id _
  have : (fun f : T ⟶ A ↦ f ≫ η.app A) = φ ∘ (fun f : T ⟶ A ↦ G.map f.op) := by
    ext f
    exact η.naturality f
  rw [this, Function.Bijective.of_comp_iff' hφ]

/-- If `f ↦ G f` is bijective on `A ⟶ A` and on `G G A ⟶ A`, the unit `η_A : A ⟶ G G A` is an
isomorphism: surjectivity on `G G A ⟶ A` gives a retraction `r` of `η_A`, and injectivity on
`A ⟶ A` turns `(η_A ≫ r) ≫ η_A = 𝟙 ≫ η_A` into `η_A ≫ r = 𝟙`. -/
theorem isIso_app_of_bijective (A : C)
    (h₁ : Function.Bijective (fun f : A ⟶ A ↦ G.map f.op))
    (h₂ : Function.Bijective (fun f : G.obj (op (G.obj (op A))) ⟶ A ↦ G.map f.op)) :
    IsIso (η.app A) := by
  rw [hη.bijective_map_op_iff] at h₁ h₂
  obtain ⟨r, hr : r ≫ η.app A = 𝟙 _⟩ := h₂.2 (𝟙 _)
  refine ⟨r, h₁.1 ?_, hr⟩
  change (η.app A ≫ r) ≫ η.app A = 𝟙 A ≫ η.app A
  rw [Category.assoc, hr]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end IsSelfDualUnit

end CategoryTheory.Functor
