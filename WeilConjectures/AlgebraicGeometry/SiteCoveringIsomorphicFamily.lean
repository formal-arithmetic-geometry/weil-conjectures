/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# A family isomorphic to a covering is a covering

## References

* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
* [Stacks Project, Tag 00VU](https://stacks.math.columbia.edu/tag/00VU)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- A family of arrows isomorphic over its target to a covering family is covering
up to a bijective reindexing, and hence is covering after reindexing.
-/
theorem site_covering_isomorphic_family
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [Precoverage.HasIsos J] [Precoverage.IsStableUnderComposition J]
    [Precoverage.IsStableUnderBaseChange J] [Precoverage.HasPullbacks J]
    {A : Type (max u v)} {U : C} {Uₐ : A → C} (g : ∀ a, Uₐ a ⟶ U)
    (hg : Presieve.ofArrows Uₐ g ∈ J U) {V : C} (φ : V ⟶ U) [IsIso φ]
    {Vₐ : A → C} (f : ∀ a, Vₐ a ⟶ V) (σ : ∀ a, Vₐ a ⟶ Uₐ a)
    (hσ : ∀ a, IsIso (σ a))
    (compat : ∀ a, σ a ≫ g a = f a ≫ φ) :
    (∃ (A' : Type (max u v)) (β : A' ≃ A),
      Presieve.ofArrows (fun a' => Vₐ (β a')) (fun a' => f (β a')) ∈ J V) ∧
      Presieve.ofArrows Vₐ f ∈ J V := by
  have hf : Presieve.ofArrows Vₐ f ∈ J V := by
    refine Precoverage.mem_coverings_of_isPullback g hg φ f σ ?_
    intro a
    have : IsIso (σ a) := hσ a
    exact IsPullback.of_vert_isIso ⟨(compat a).symm⟩
  exact ⟨⟨A, Equiv.refl A, hf⟩, hf⟩

end CategoryTheory
