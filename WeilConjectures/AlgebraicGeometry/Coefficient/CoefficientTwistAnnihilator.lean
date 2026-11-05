/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement

/-! # An annihilating exponent for finite coefficient Tate twists

Source: coefficient twists, the choice of the fixed Kummer exponent
(blueprint: lem-coefficient-twist-annihilator).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.ProEtale
