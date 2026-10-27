/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-! # Unique lifts to the simplex presentation

Source: Stacks Project, Tag 0168, `lemma-face-degeneracy-category` (a),(c),
as used in Tag 016B, `lemma-characterize-simplicial-object` (2).
(blueprint: lem-trf-simplex-presentation-unique-lifts)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace SimplexCategoryGenRel

/-- Every simplex arrow has a unique lift to the generators-and-relations presentation.
The lifts preserve identities, composition, cofaces and codegeneracies, and form a functor
fixing degree labels which is a strict two-sided inverse to `toSimplexCategory`.

Source: Stacks Project, Tag 0168, `lemma-face-degeneracy-category` (a),(c),
as used in Tag 016B, `lemma-characterize-simplicial-object` (2).
(blueprint: lem-trf-simplex-presentation-unique-lifts)

Proof: (1) Let W be the property of a simplex arrow admitting a presentation arrow with
exactly the same degree labels and the prescribed image. Identity arrows and the coface
and codegeneracy generators witness W. Composition of witnesses witnesses composition,
since `toSimplexCategory` is a functor.
(2) Apply `SimplexCategory.morphismProperty_eq_top`
(lem-sc-simplex-morphism-property-generators) to W to obtain a lift of every arrow.
(3) Apply `simplexPresentation_faithful`
(lem-sc-module-cup-godement-simplex-presentation-faithful) to two lifts with the same image;
they are equal. Choose the uniquely determined lift for each arrow.
(4) Identities, composites of lifts, and generators have the required images, so uniqueness
identifies them with the corresponding lifts. These equations define the inverse functor
K on objects and arrows. The image of each lift is the original arrow, so K followed by J
is the identity. Conversely, a presentation arrow and the lift of its image have the same
image, so uniqueness gives the other strict inverse equality, including on all objects. -/
theorem unique_lifts :
    ∃ lift : ∀ {m n : ℕ},
        (SimplexCategory.mk m ⟶ SimplexCategory.mk n) → (mk m ⟶ mk n),
      (∀ {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n),
        toSimplexCategory.map (lift α) = α ∧
          ∀ f : mk m ⟶ mk n, toSimplexCategory.map f = α → f = lift α) ∧
      (∀ n : ℕ, lift (𝟙 (SimplexCategory.mk n)) = 𝟙 (mk n)) ∧
      (∀ {m n p : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
        (β : SimplexCategory.mk n ⟶ SimplexCategory.mk p),
        lift (α ≫ β) = lift α ≫ lift β) ∧
      (∀ {n : ℕ} (i : Fin (n + 2)), lift (SimplexCategory.δ i) = δ i) ∧
      (∀ {n : ℕ} (i : Fin (n + 1)), lift (SimplexCategory.σ i) = σ i) ∧
      ∃ K : SimplexCategory ⥤ SimplexCategoryGenRel,
        (∀ n : ℕ, K.obj (SimplexCategory.mk n) = mk n) ∧
        (∀ {m n : ℕ} (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n),
          HEq (K.map α) (lift α)) ∧
        K ⋙ toSimplexCategory = 𝟭 SimplexCategory ∧
        toSimplexCategory ⋙ K = 𝟭 SimplexCategoryGenRel := by
  sorry

end SimplexCategoryGenRel
