/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Lisse Weil sheaves on a smooth curve and dense opens

If `F` is a lisse Weil sheaf on a smooth curve `C₀` over `k₀` and `j : U₀ ⟶ C₀` is a dense
quasi-compact open immersion, then the adjunction unit `F ⟶ j_* j^* F` is an isomorphism
(blueprint: `lem-a1-lisse-middle-extension`), and `j^*` carries irreducible lisse sheaves to
irreducible lisse sheaves (blueprint: `lem-wf-dense-open-pi1-surjective`, part (4)). Both
reflect the surjectivity of the map of Weil groups `W(U₀) ⟶ W(C₀)`. The étale finite-coefficient
version of the first statement is `AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsLisse.isIso_unit_app`: blueprint
  `lem-a1-lisse-middle-extension`.
- `AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`: its consequence
  `F ≅ j_* j^* F`.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar`: blueprint
  `lem-wf-dense-open-pi1-surjective`, part (4).
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

/-- **Restriction to a dense open preserves irreducibility.** Let `C₀` be a smooth curve over
`k₀` and `j : U₀ ⟶ C₀` an open immersion with dense image. The pullback `j^*` carries an
irreducible lisse Weil sheaf on `C₀` (one without lisse subsheaves other than `0` and itself) to
an irreducible lisse Weil sheaf on `U₀`: lisse Weil sheaves are representations of the Weil
groups on the generic stalk, and the map `W(U₀) ⟶ W(C₀)` is surjective, so the stable subspaces
of the stalk are the same. The blueprint states this for a geometrically connected curve; the
argument applies to each connected component, all of which meet the dense `U₀`.
(blueprint: `lem-wf-dense-open-pi1-surjective`, part (4)) -/
theorem WeilSheaf.IsIrreducibleLisse.upperStar {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsIrreducibleLisse) :
    ((WeilSheaf.upperStar j).obj F).IsIrreducibleLisse := by
  -- TODO(adic): the equivalence between lisse Weil sheaves and representations of the Weil
  -- group, and the surjectivity of `W(U₀) ⟶ W(C₀)` for Weil sheaves, are not yet available
  sorry

end AlgebraicGeometry
