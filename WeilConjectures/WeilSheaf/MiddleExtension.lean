/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil

/-!
# Lisse Weil sheaves on a smooth curve and dense opens

If `F` is a lisse Weil sheaf on a smooth curve `C₀` over `k₀` and `j : U₀ ⟶ C₀` is a dense
quasi-compact open immersion, then the adjunction unit `F ⟶ j_* j^* F` is an isomorphism
(blueprint: `lem-a1-lisse-middle-extension`), reflecting the surjectivity of the map of Weil
groups `W(U₀) ⟶ W(C₀)`. The étale finite-coefficient version is
`AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.isIso_unit_app`: blueprint
  `lem-a1-lisse-middle-extension`.
- `AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`: its consequence
  `F ≅ j_* j^* F`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Recovery from a dense lisse open.** Let `C₀` be a smooth curve over `k₀`, `j : U₀ ⟶ C₀` a
quasi-compact open immersion with dense image and `F` a lisse Weil sheaf on `C₀`. Then the
adjunction unit `F ⟶ j_* j^* F` is an isomorphism: on `U₀` this is clear, and at a removed point
`x` the stalk of `j_* j^* F` is the inertia invariants `(F_η̄)^{I_x} = F_x̄`, the inertia acting
trivially since `F` is lisse at `x`. (blueprint: `lem-a1-lisse-middle-extension`; also
`lem-wf-dense-open-pi1-surjective`, part (3)) -/
theorem WeilSheaf.IsLisse.isIso_unit_app {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    IsIso ((WeilSheaf.upperStarLowerStarAdjunction j).unit.app F) := by
  -- TODO(adic): the stalk computation at the removed points
  -- (blueprint `lem-wf-boundary-stalk-invariants`) is not yet available
  sorry

/-- **Recovery from a dense lisse open**, `F ≅ j_* j^* F` for a lisse Weil sheaf `F` on a smooth
curve and a dense open immersion `j` (`AlgebraicGeometry.WeilSheaf.IsLisse.isIso_unit_app`).
(blueprint: `lem-a1-lisse-middle-extension`) -/
theorem WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    Nonempty (F ≅ (WeilSheaf.directImage j).obj ((WeilSheaf.upperStar j).obj F)) :=
  have := hF.isIso_unit_app j hj
  ⟨asIso ((WeilSheaf.upperStarLowerStarAdjunction j).unit.app F)⟩

end AlgebraicGeometry
