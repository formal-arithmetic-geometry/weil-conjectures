/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Bounded constructible derived-complete integral coefficients

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
order 1459 (blueprint: def-weil-derived-complete-integral-detailed).
The integral triangulation statement compiles this same canonical interface in a
paired source packet to retain its recorded independent coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace WeilConjectures

end WeilConjectures

/- Stage-2 paired-interface rebuild for NZ integral Tor triangulation. -/
