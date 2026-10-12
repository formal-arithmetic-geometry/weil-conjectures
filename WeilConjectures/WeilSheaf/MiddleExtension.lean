/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

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
`F ≅ j_* j^* F`, by the adjunction unit: on the geometric fibre it is the unit of `j̄^* ⊣ j̄_*` at a
lisse sheaf, which is invertible (blueprint: `lem-wf-dense-open-pi1-surjective`, part (3)).
(blueprint: `lem-a1-lisse-middle-extension`)

The blueprint node asks for the adjunction unit `F ⟶ j_* j^* F` to be an isomorphism; the
isomorphism constructed here is that unit. -/
theorem WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l C} (hF : F.IsLisse) :
    Nonempty (F ≅ (WeilSheaf.directImage j).obj ((WeilSheaf.upperStar j).obj F)) := by
  have : IsDominant j := ⟨hj⟩
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : IsIso ((Endofunctor.IsoAlgebra.forget _).map
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).unit.app F.obj)) :=
    ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_geometricFiberMap (k₀ := k₀) j
      F.obj.carrier hF
  have : IsIso ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).unit.app F.obj) :=
    isIso_of_reflects_iso _ (Endofunctor.IsoAlgebra.forget _)
  exact ⟨ObjectProperty.isoMk _
    (asIso ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j).unit.app F.obj))⟩

end AlgebraicGeometry
