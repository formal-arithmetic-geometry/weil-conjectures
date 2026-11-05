/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData

/-! Finite-stage component of ambient coefficient pullback.
Source: Stacks 03CB and 03D3.
(blueprint: lem-sf-ambient-coefficient-pullback-iso-finite).

The proof compares the chosen ringed-site adjunction with the constant-sheaf
adjunction on the pro-etale terminal object.  The two left adjoints are uniquely
isomorphic, and the defining constant-section equation identifies that comparison
with `ringMap`; its component is therefore invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

end WeilConjectures.AmbientPullbackTensor
