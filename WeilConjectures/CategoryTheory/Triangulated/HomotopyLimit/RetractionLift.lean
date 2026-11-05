/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete

/-!
# Lifting compatible retractions to a complete object

Let `C` be a pretriangulated category, `z` an element of the center of `C` commuting with the
shifts (for instance the multiplication by an integer `m`) and `A` a `z`-complete object
(`CategoryTheory.Pretriangulated.IsCenterComplete`). Think of `A` as a complex of
`ℤ_ℓ`-modules, `z = ℓ`, and of objects `Qₙ` as its reductions `A ⊗ᴸ ℤ/ℓⁿ⁺¹`, with the reduction
maps `η₀ : A ⟶ Q₀`, the transitions `tₙ : Qₙ₊₁ ⟶ Qₙ` and the Bockstein maps `δₙ : Qₙ ⟶ A⟦1⟧`,
which satisfy `tₙ ≫ δₙ = δₙ₊₁ ≫ z` and such that `A --z--> A --η₀--> Q₀ --δ₀--> A⟦1⟧` is
distinguished.

* `CategoryTheory.Pretriangulated.IsCenterComplete.eq_zero_of_comp_app_eq`: a family of maps
  `oₙ : B ⟶ K` into a complete object with `oₙ₊₁ ≫ z = oₙ` vanishes. It is a cone over the tower
  `⋯ --z--> K --z--> K`, whose homotopy limit vanishes.
* `CategoryTheory.Pretriangulated.exists_comp_eq_of_tower`: a compatible family of maps
  `ρₙ : B ⟶ Qₙ` lifts at level `0` to a map `r : B ⟶ A` with `r ≫ η₀ = ρ₀`. The obstruction
  `ρ₀ ≫ δ₀` is the first term of the family `ρₙ ≫ δₙ`, which vanishes by the previous point.
  This is the surjectivity half of the Milnor sequence for `A = R lim Qₙ`; no `lim¹` term has
  to vanish.
* `CategoryTheory.Pretriangulated.isSplitMono_of_tower`: **lifting split monomorphisms**. Let
  `i : A ⟶ B` and let `ρₙ : B ⟶ Qₙ` be compatible with `i ≫ ρ₀ = η₀`, for instance
  `ρₙ = ηₙ(B) ≫ rₙ` for compatible retractions `rₙ` of the reductions of `i`. If every
  endomorphism `e` of `A` with `e ≫ η₀ = η₀` is invertible (derived Nakayama), then `i` is a
  split monomorphism: for the lift `r` of `ρ₀`, `i ≫ r` is such an endomorphism, and
  `r ≫ (i ≫ r)⁻¹` is a retraction of `i`.

That complete objects are stable under shifts and extensions
(`CategoryTheory.Pretriangulated.IsCenterComplete.shift`,
`CategoryTheory.Pretriangulated.IsCenterComplete.ext₂`) is in
`WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete`.
-/

@[expose] public section

namespace CategoryTheory.CatCenter

variable {D : Type*} [Category* D] [Preadditive D]

end CategoryTheory.CatCenter

namespace CategoryTheory.Pretriangulated

open Category Limits _root_.Opposite

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable {z : CatCenter C} (hz : ∀ (X : C) (n : ℤ), z.app (X⟦n⟧) = (z.app X)⟦n⟧') {A : C}
  (hA : IsCenterComplete z A) [HasProduct fun _ : ℕ ↦ A⟦(1 : ℤ)⟧] {Q : ℕ → C} (η₀ : A ⟶ Q 0)
  (t : ∀ n, Q (n + 1) ⟶ Q n) (δ : ∀ n, Q n ⟶ A⟦(1 : ℤ)⟧)
  (hδ : ∀ n, t n ≫ δ n = δ (n + 1) ≫ z.app (A⟦(1 : ℤ)⟧)) (a : A ⟶ A)
  (hT : Triangle.mk a η₀ (δ 0) ∈ distTriang C)
include hz hA hδ hT

end CategoryTheory.Pretriangulated
