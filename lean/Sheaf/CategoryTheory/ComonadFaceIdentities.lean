/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.NaturalTransportInduction

/-! # Whiskered counit face identities

Source: literature/stacks-project/simplicial.tex, Example 0G5M and Lemma 0G5N,
proof of condition (1)(a); categories.tex, Tag 003F
(blueprint: lem-trf-comonad-face-identities).

The index `n` on `d` stands for source degree `n + 1`: its source is `T^(n+2)`
and its target is `T^(n+1)`. The normalization fixes each natural transformation
as the specified horizontal composite. Heterogeneous equality identifies the
recursive powers with their expanded composites, without arbitrary comparison maps.
Mathlib's `◫` writes the inner factor first, reversing the order of the source's `⋆`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

/-- Whiskering any natural transformation `e : T ⟶ 𝟭 C` gives natural face operators,
with both deletion orders equal to the displayed double horizontal composite.
No comultiplication or counit equation is required.

Source: literature/stacks-project/simplicial.tex, Example 0G5M and Lemma 0G5N,
proof opening and condition (1)(a); categories.tex, Tag 003F
(blueprint: lem-trf-comonad-face-identities).

Proof plan:
1. From def-trf-endofunctor-powers, induction gives the object and morphism identities
   `T^(r+s) = T^r ∘ T^s`. Expand horizontal composition to obtain the component
   `T^i(e_(T^(n-i) x))` of the face in degree `n`. Naturality of `e` at
   `T^(n-i)(f)`, followed by `T^i`, proves naturality of this component family.
2. For the two positions `i < j`, put `a = i`, `b = j-i-1`, `c = n+1-j`,
   and `y = T^c x`. The two composites have components respectively
   `T^a(e_(T^b y) ∘ T^(b+1)(e_y))` and
   `T^a(T^b(e_y) ∘ e_(T^(b+1) y))`. Naturality of `e` at `T^b(e_y)`
   identifies them; equality at every object identifies the natural transformations.
3. Expand the left-associated horizontal word `1_a ⋆ e ⋆ 1_b ⋆ e ⋆ 1_c`.
   Its component is the first component in step 2, proving the second equality.
   Zero values of `a`, `b`, and `c` use the identity functor, so the argument
   includes the first face, adjacent deletions, and the last face.

The existential family is fixed by its horizontal-composite normalization; it does not
assume any face identities. In the last clause `j.succ` is the source's larger index,
so `i ≤ j` is exactly the source's strict inequality `i < j+1`. -/
theorem comonad_face_identities
    {C : Type u} [Category.{v} C] (T : C ⥤ C) (e : T ⟶ 𝟭 C) :
    ∃ d : ∀ n : ℕ, Fin (n + 2) →
        (NaturalTransport.power T (n + 2) ⟶ NaturalTransport.power T (n + 1)),
      (∀ (n : ℕ) (i : Fin (n + 2)), HEq (d n i)
        ((𝟙 (NaturalTransport.power T (n + 1 - i.val))) ◫ e ◫
          (𝟙 (NaturalTransport.power T i.val)))) ∧
      ∀ (n : ℕ) (i j : Fin (n + 2)), i ≤ j →
        (d (n + 1) j.succ ≫ d n i = d (n + 1) i.castSucc ≫ d n j) ∧
        HEq (d (n + 1) j.succ ≫ d n i)
          ((𝟙 (NaturalTransport.power T (n + 1 - j.val))) ◫ e ◫
            (𝟙 (NaturalTransport.power T (j.val - i.val))) ◫ e ◫
            (𝟙 (NaturalTransport.power T i.val))) := by
  sorry

end CategoryTheory
