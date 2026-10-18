/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Pretriangulated categories with countable coproducts are idempotent complete

Let `C` be a pretriangulated category with coproducts indexed by `Type v` (the universe of its
`Hom`-types). Then `C` is idempotent complete
(`CategoryTheory.Pretriangulated.isIdempotentComplete_of_hasCoproducts`, Bökstedt–Neeman, Stacks
Tag 05QW, blueprint `det-brown-hypotheses-ambient`).

For an idempotent `e : A ⟶ A`, let `Z` be the telescope (homotopy colimit) of
`A ⟶[e] A ⟶[e] A ⟶ ⋯`, the third object of a distinguished triangle
`∐ₙ A ⟶[𝟙 - t] ∐ₙ A ⟶[π] Z ⟶ (∐ₙ A)⟦1⟧`. Precomposition with `𝟙 - t` is surjective on morphisms
out of `∐ₙ A` (`CategoryTheory.Pretriangulated.IdempotentTelescope.exists_comp_eq`), so `π` is
an epimorphism, and `Z` is an image of `e`: the maps `A ⟶ Z` (via the summand `0`) and
`Z ⟶ A` (induced by `e` on each summand) split `e`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Category Preadditive

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasCoproducts.{v} C]

namespace IdempotentTelescope

open BrownRepresentability Telescope

variable {A : C} {e : A ⟶ A} (he : e ≫ e = e)
include he

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- For an idempotent `e : A ⟶ A`, precomposition with `𝟙 - t` is surjective on morphisms out of
`∐ₙ A`, where `t` is the shift of the sequence `A ⟶[e] A ⟶[e] ⋯`: a family `hₙ : A ⟶ W` is the
image of `gₙ = (𝟙 - e) ≫ hₙ - ∑_{j < n} e ≫ hⱼ`. -/
lemma exists_comp_eq {W : C} (h : sum (fun _ : ℕ ↦ A) ⟶ W) :
    ∃ g, (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) ≫ g = h := by
  refine ⟨Sigma.desc fun k ↦ (𝟙 A - e) ≫ ι (fun _ : ℕ ↦ A) k.down ≫ h -
    ∑ j ∈ Finset.range k.down, e ≫ ι (fun _ : ℕ ↦ A) j ≫ h, ?_⟩
  refine hom_ext _ fun n ↦ ?_
  rw [sub_comp, comp_sub, id_comp, ι_shift_assoc, ι_desc, ι_desc]
  simp only [comp_sub, comp_add, comp_sum, Finset.sum_range_succ, ← assoc, he, sub_comp, id_comp,
    sub_self]
  abel

variable {Z : C} {π : sum (fun _ : ℕ ↦ A) ⟶ Z} {δ : Z ⟶ (sum (fun _ : ℕ ↦ A))⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) π δ ∈ distTriang C)
include hT

/-- The map `π : ∐ₙ A ⟶ Z` to the telescope of an idempotent is an epimorphism. -/
lemma epi_π : Epi π := by
  refine ⟨fun {W} u₁ u₂ hu ↦ ?_⟩
  rw [← sub_eq_zero]
  have hu' : π ≫ (u₁ - u₂) = 0 := by rw [comp_sub, hu, sub_self]
  obtain ⟨h, hh⟩ : ∃ h : (sum (fun _ : ℕ ↦ A))⟦(1 : ℤ)⟧ ⟶ W, u₁ - u₂ = δ ≫ h :=
    Triangle.yoneda_exact₃ _ hT (u₁ - u₂) hu'
  let adj := (shiftEquiv' C (1 : ℤ) (-1) (by norm_num)).toAdjunction
  obtain ⟨g, hg⟩ := exists_comp_eq he (adj.homEquiv _ _ h)
  have : h = (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e))⟦(1 : ℤ)⟧' ≫
      (adj.homEquiv _ _).symm g := by
    have := adj.homEquiv_naturality_left_symm (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) g
    rw [hg, Equiv.symm_apply_apply] at this
    exact this
  have h₀ : δ ≫ (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e))⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hT
  rw [hh, this, ← assoc, h₀, zero_comp]

/-- In the telescope of an idempotent `e`, the maps `A ⟶ Z` from the summands are invariant
under `e`. -/
lemma e_comp_ι_π (n : ℕ) : e ≫ ι (fun _ : ℕ ↦ A) n ≫ π = ι (fun _ : ℕ ↦ A) n ≫ π := by
  rw [ι_π hT n, ← assoc, he]

/-- In the telescope of an idempotent, all the maps `A ⟶ Z` from the summands agree. -/
lemma ι_π_eq (n : ℕ) : ι (fun _ : ℕ ↦ A) n ≫ π = ι (fun _ : ℕ ↦ A) 0 ≫ π := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ι_π hT n, e_comp_ι_π he hT]

/-- The telescope `Z` of an idempotent `e : A ⟶ A` is an image of `e`: there are `r : Z ⟶ A`
and `i : A ⟶ Z` with `r ≫ i = 𝟙 Z` and `i ≫ r = e`. -/
lemma exists_split : ∃ (r : Z ⟶ A) (i : A ⟶ Z), r ≫ i = 𝟙 Z ∧ i ≫ r = e := by
  have := epi_π he hT
  let g : sum (fun _ : ℕ ↦ A) ⟶ A := Sigma.desc fun _ ↦ e
  have hg : (𝟙 _ - shift (fun _ : ℕ ↦ A) (fun _ ↦ e)) ≫ g = 0 := by
    refine hom_ext _ fun n ↦ ?_
    simp [g, he]
  obtain ⟨r, hr⟩ : ∃ r : Z ⟶ A, g = π ≫ r := Triangle.yoneda_exact₂ _ hT g hg
  refine ⟨r, ι (fun _ : ℕ ↦ A) 0 ≫ π, ?_, ?_⟩
  · rw [← cancel_epi π, ← assoc, ← hr, comp_id]
    refine hom_ext _ fun n ↦ ?_
    rw [ι_desc_assoc, ι_π_eq he hT n, e_comp_ι_π he hT]
  · rw [assoc, ← hr, ι_desc]

end IdempotentTelescope

open IdempotentTelescope in
/-- A pretriangulated category with coproducts indexed by `Type v` is idempotent complete
(Bökstedt–Neeman, Stacks Tag 05QW): an idempotent `e` splits through the telescope of
`A ⟶[e] A ⟶[e] ⋯`. -/
theorem isIdempotentComplete_of_hasCoproducts : IsIdempotentComplete C := by
  refine ⟨fun A e he ↦ ?_⟩
  obtain ⟨Z, π, δ, hT⟩ := distinguished_cocone_triangle
    (𝟙 _ - BrownRepresentability.Telescope.shift (fun _ : ℕ ↦ A) (fun _ ↦ e))
  obtain ⟨r, i, h₁, h₂⟩ := exists_split he hT
  exact ⟨Z, r, i, h₁, h₂⟩

end CategoryTheory.Pretriangulated
