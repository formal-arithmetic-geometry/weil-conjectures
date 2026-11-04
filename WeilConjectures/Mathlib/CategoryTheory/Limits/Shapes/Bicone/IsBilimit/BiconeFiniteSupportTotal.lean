/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The total relation for a bicone with finite support

Source: the finite graded direct sum in the filtered Hom formula and the final factorization
in the latest blueprint `sk-i-additivity.proof.md`
(blueprint: lem-trf-bicone-finite-support-total).
-/

@[expose] public section
set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.Bicone

/-- A bilimit bicone is the sum of its projections followed by its inclusions over any
finite set containing its nonzero summands.

Source: latest blueprint `sk-i-additivity.proof.md`, the finite weight-zero Hom sum
(blueprint: lem-trf-bicone-finite-support-total).
Proof: test the proposed identity against every projection, using the product universal
property. On a supported index the bicone relations leave precisely that projection. On
an unsupported index both sides vanish because the target summand is zero. This also
covers an empty support and a zero bicone. -/
theorem IsBilimit.total_of_isZero {J : Type w} {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] {f : J → C} {b : Bicone f}
    (hb : b.IsBilimit) (s : Finset J) (hs : ∀ j, j ∉ s → IsZero (f j)) :
    ∑ j ∈ s, b.π j ≫ b.ι j = 𝟙 b.pt := by
  classical
  apply hb.isLimit.hom_ext
  intro j
  change (∑ k ∈ s, b.π k ≫ b.ι k) ≫ b.π j.as = (𝟙 b.pt) ≫ b.π j.as
  by_cases hj : j.as ∈ s
  · calc
      (∑ k ∈ s, b.π k ≫ b.ι k) ≫ b.π j.as =
          ∑ k ∈ s, if k = j.as then b.π j.as else 0 := by
        rw [Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = j.as
        · subst k
          simp
        · simp [Category.assoc, b.ι_π, hk]
      _ = (𝟙 b.pt) ≫ b.π j.as := by simp [hj]
  · exact (hs j.as hj).eq_of_tgt _ _

end CategoryTheory.Limits.Bicone
