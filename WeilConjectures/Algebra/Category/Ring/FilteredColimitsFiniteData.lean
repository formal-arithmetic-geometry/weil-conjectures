/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Finite data and finite relations descend in a filtered colimit of rings

Let `c` be a colimit cocone over a filtered diagram `F` of commutative rings. Finitely many
elements `x : σ → c.pt` of the colimit satisfying finitely many polynomial identities
`P l (x) = Q l (x)` (with `P l, Q l : MvPolynomial σ ℤ`) lift to a common stage `F.obj j` such
that the identities already hold there, and hence after every transition `F.obj j ⟶ F.obj k`.

## Main results

- `CommRingCat.exists_map_eq_zero_of_finset`: finitely many elements of a stage that vanish in
  the colimit vanish at a later stage.
- `CommRingCat.exists_lift_forall_aeval_eq`: the statement above.
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits

namespace CommRingCat

section

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ CommRingCat.{u})
  (c : Cocone F) [PreservesColimit F (forget CommRingCat)] (hc : IsColimit c)

include hc in
/-- Finitely many elements of a stage of a filtered colimit of rings which vanish in the colimit
vanish at a common later stage. -/
lemma exists_map_eq_zero_of_finset {j : J} (s : Finset (F.obj j))
    (hs : ∀ x ∈ s, c.ι.app j x = 0) : ∃ (k : J) (α : j ⟶ k), ∀ x ∈ s, F.map α x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, α, hα⟩ := ih fun x hx ↦ hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨k', β, _, hβ⟩ := Concrete.isColimit_exists_of_rep_eq F hc a 0
      (by rw [hs a (Finset.mem_insert_self a s), map_zero])
    rw [map_zero] at hβ
    let l := IsFiltered.leftToMax k k'
    let r := IsFiltered.rightToMax k k'
    let m := IsFiltered.coeqHom (α ≫ l) (β ≫ r)
    have hm : α ≫ l ≫ m = β ≫ r ≫ m := by
      simpa only [Category.assoc] using IsFiltered.coeq_condition (α ≫ l) (β ≫ r)
    refine ⟨_, α ≫ l ≫ m, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [hm, Functor.map_comp, CommRingCat.comp_apply, hβ, map_zero]
    · rw [Functor.map_comp, CommRingCat.comp_apply, hα x hx, map_zero]

end

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  {c : Cocone F} [PreservesColimit F (forget CommRingCat)]

end CommRingCat
