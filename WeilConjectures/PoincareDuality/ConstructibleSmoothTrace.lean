/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTraceUnit

/-! # Smooth trace without an additional exceptional-adjoint hypothesis

Source: latest blueprint sk-def-sp-trace, normalized constructible counit.
The uniquely normalized purity family already constructs its restricted adjunction.
(blueprint: sk-def-sp-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The counit of the uniquely integration-normalized constructible adjunction.
Right-adjoint uniqueness identifies it with compact support of gamma followed by the
constructible exceptional counit. Consequently this is the same smooth trace on all
admissible stages, with no supplied ambient exceptional-adjoint datum.
Source: the purity-then-counit display (blueprint: sk-def-sp-trace). -/
def constructibleSmoothTrace (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (s : SmoothDatum D) (K : c.ctf ell s.Y.left) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj ((c.smoothSource ell s.map s.dim).obj K.obj) ⟶
        K.obj :=
  (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s).trace K

end AlgebraicGeometry.ProEtale.PurityTransport
