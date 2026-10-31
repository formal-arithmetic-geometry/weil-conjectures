/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent

/-! # Smooth trace for admissible condensed coefficients

Source: latest blueprint, sec-smooth-purity/sk-def-sp-trace/_section.md,
the displayed purity-then-counit composite (blueprint: sk-def-sp-trace).

The coefficient presentations, Tate lines, finite-Tor constructible categories,
compact-support functor and normalized purity family are the recorded ones.
The Brown adjunction is displayed in the existing `ScalarExceptionalAdjoint` interface;
its restricted counit is the restriction of that very adjunction's counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The smooth trace on every finite-Tor constructible complex, for every admissible
coefficient presentation. The supplied localizing adjunction is the specified Brown
adjunction, restricted with its actual counit. The existing canonical purity comparison
uses the uniquely integration-normalized family and right-adjoint uniqueness.
Apply compact support to that gamma and compose with the restricted Brown counit.
Source: latest blueprint sec-smooth-purity/sk-def-sp-trace/_section.md,
the displayed two-arrow composite (blueprint: sk-def-sp-trace). -/
def smoothTrace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (s : SmoothDatum D)
    (R : CondensedRing.ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
    (K : c.ctf ell s.Y.left) :
    R.lower.obj ((source ell c s.map s.dim
      (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s).source_closed).obj K) ⟶
        K :=
  R.lower.map
    ((WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c s R).hom.app K) ≫
      R.restrictedAdjunction.counit.app K

end AlgebraicGeometry.ProEtale.PurityTransport
