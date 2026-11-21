/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting

/-! # Forgetting the constant vector-space action of a native adic module

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
variable (l : ℕ) [Fact l.Prime]

/-- The action of constant coefficient functions recovers the forgotten vector-space action. -/
theorem native_adic_forgetAb_isEquivalence (T : Scheme.{u}) :
    (ProEtale.AdicSheaf.forgetAb l T).IsEquivalence := by
  exact ProEtale.nativeScalarForgetting_isEquivalence l T

end WeilConjectures.LocallyFiniteAdicCompactSupport
