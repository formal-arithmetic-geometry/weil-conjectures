/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FibredRelativeCech

/-! # Contraction from a section up to 2-isomorphism

Source: Stacks Project, Tag 06XA, via Tag 06X6
(blueprint: lem-sfb-split-fibred-cech-contraction).

The natural transformations below are between endofunctors of abelian sheaves.
Their naturality includes every coefficient morphism, for the fixed section.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- A specified 2-section contracts the entire augmented relative Cech complex,
including the augmentation identity, naturally in the abelian coefficient sheaf.
Source: Stacks Project, Tag 06XA, via 06X6
(blueprint: lem-sfb-split-fibred-cech-contraction).

Proof: use lem-sfb-relative-cech-presentation-comparison to pass to common-target
 tuples, with the identity comparison in degree -1. Write `t : f s ≅ id`.
Prepend `(s(y), t_y)` to each tuple and send an arrow `(b_i,c)` to
`(s(c),b_i,c)`. Naturality of `t` verifies the arrow equation, so this is a
functor strictly over the common target. Deleting the new entry gives the
identity; deleting old entry `j` agrees with insertion after deleting `j`.
Pullback of compatible families along these insertion functors defines `h` in
positive degrees. In degree zero evaluate at `(s(x),x,t_x)` over the identity
base arrow; the arrow `(s(c),c)` proves compatibility with every restriction.
These additive natural transformations are sheaf morphisms. The first face
identity gives augmentation followed by evaluation equal to the identity.
For degree `p >= 0`, expand the alternating differential after insertion.
The new first face contributes the identity; shifting all remaining face
indices by one gives minus the differential after `h`. This proves the other
homotopy identity, including degree zero where the remaining face is the
augmentation. Evaluation and precomposition commute with every coefficient
morphism. Finally conjugate by the presentation comparison, natural in the
coefficients and the identity at degree -1. No covering or faithfulness
assumption enters any step. -/
theorem splitFibredCech_contraction {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} (f : BasedFunctor U X)
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (s : BasedFunctor X U) (t : ModuliTwoIso (s.comp f) (BasedFunctor.id X)) :
    ∃ h : (n : ℕ) →
        fibredRelativeCechTerm f hU hX (n + 1) ⟶ fibredRelativeCechTerm f hU hX n,
      fibredRelativeCechDifferential f hU hX 0 ≫ h 0 = 𝟙 _ ∧
      ∀ n : ℕ, h n ≫ fibredRelativeCechDifferential f hU hX n +
        fibredRelativeCechDifferential f hU hX (n + 1) ≫ h (n + 1) = 𝟙 _ := by
  sorry

end CategoryTheory
