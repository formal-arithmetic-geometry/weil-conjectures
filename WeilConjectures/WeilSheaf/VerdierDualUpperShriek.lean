/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierDual

/-!
# The Verdier dual of the exceptional inverse image of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
`𝔻_X (Rf^! L) ≅ f^* (𝔻_Y L)` for every Weil complex `L` on `Y` (blueprint
`corollary-verdier-exchange-formulas--4`, at the coefficient stage `ℚ̄_ℓ`): dualize
`Rf^! L ≅ 𝔻_X f^* 𝔻_Y L` (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_iso`) and use
biduality on `X`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_verdierDual_rightOp_comp_verdierDual`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `corollary-verdier-exchange-formulas--4`: the dual of the exceptional inverse image
of Weil complexes, `𝔻_X (Rf^! L) ≅ f^* (𝔻_Y L)`. -/
theorem nonempty_verdierDual_upperShriek_obj_iso [HasUpperShriek k₀ l f]
    (L : WeilComplex k₀ l Y) :
    Nonempty ((verdierDual k₀ l X).obj (op ((upperShriek f).obj L)) ≅
      (upperStar f).obj ((verdierDual k₀ l Y).obj (op L))) := by
  obtain ⟨e⟩ := nonempty_upperShriek_obj_iso f L
  obtain ⟨eX⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l X
  exact ⟨(verdierDual k₀ l X).mapIso e.op.symm ≪≫ (eX.app _).symm⟩

end WeilComplex

end AlgebraicGeometry
