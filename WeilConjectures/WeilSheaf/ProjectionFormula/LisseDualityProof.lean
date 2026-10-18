/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseDuality
public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseDualityAssembly

/-!
# Duality for lisse pro-étale Weil sheaves, unconditionally

The internal hom out of a pro-étale Weil sheaf with lisse underlying sheaf is the tensor product
with its dual (`AlgebraicGeometry.ProEtaleWeilSheaf.lisseDuality`), by the duality of lisse
`ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_tensorDualToIhom`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Duality for lisse pro-étale Weil sheaves**: `[M, -] ≅ - ⊗ M^∨` for a pro-étale Weil sheaf
`M` with lisse underlying sheaf. -/
theorem lisseDuality : LisseDuality k₀ l :=
  lisseDuality_of_isIso fun hM N ↦ hM.isIso_tensorDualToIhom N

end AlgebraicGeometry.ProEtaleWeilSheaf
