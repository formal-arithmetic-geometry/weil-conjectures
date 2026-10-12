/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# A lisse Weil sheaf on a smooth curve is the middle extension of its restriction

If `F` is a lisse Weil sheaf on a smooth curve `C₀` over `k₀` and `j : U₀ ⟶ C₀` is a dense
quasi-compact open immersion, then `F ≅ j_* j^* F` (blueprint: `lem-a1-lisse-middle-extension`).
The étale finite-coefficient version is
`AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`: blueprint
  `lem-a1-lisse-middle-extension`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Recovery from a dense lisse open.** Let `C₀` be a smooth curve over `k₀`, `j : U₀ ⟶ C₀` a
quasi-compact open immersion with dense image and `F` a lisse Weil sheaf on `C₀`. Then
`F ≅ j_* j^* F`: on `U₀` this is clear, and at a removed point `x` the stalk of `j_* j^* F` is
the inertia invariants `(F_η̄)^{I_x} = F_x̄`, the inertia acting trivially since `F` is lisse at
`x`. (blueprint: `lem-a1-lisse-middle-extension`)

This is a weakening of the blueprint node, which asks for the adjunction unit
`F ⟶ j_* j^* F` to be an isomorphism; here only some isomorphism is asserted. -/
theorem WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    Nonempty (F ≅ (WeilSheaf.directImage j).obj ((WeilSheaf.upperStar j).obj F)) := by
  -- TODO(adic): the Weil-sheaf adjunction `j^* ⊣ j_*` and the stalk computation at the removed
  -- points (blueprint `lem-wf-boundary-stalk-invariants`) are not yet available
  sorry

end AlgebraicGeometry
