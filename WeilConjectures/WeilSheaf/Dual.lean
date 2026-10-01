/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# The dual and the geometric coinvariants of a Weil sheaf

Placeholders with `sorry` bodies; see `WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.dual`: the dual of a lisse Weil sheaf.
- `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`: the geometric coinvariants of a lisse
  Weil sheaf, with the Frobenius induced from the Weil structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

-- TODO(unify): sk-d-real-operations
/-- The dual `F ↦ F ∨` of a lisse Weil sheaf. -/
noncomputable def dual (F : WeilSheaf k₀ l X) : WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-operations
/-- The coinvariants `V_{π₁(X ⊗ k)}` of the generic geometric representation of a lisse Weil
sheaf, with the Frobenius induced from the Weil structure: the maximal geometrically constant
quotient of `F`. -/
noncomputable def geometricCoinvariants (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) := sorry

end WeilSheaf

end AlgebraicGeometry
