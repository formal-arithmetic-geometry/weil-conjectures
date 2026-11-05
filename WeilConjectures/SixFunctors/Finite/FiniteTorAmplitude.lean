/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude

/-!
# Constructible coefficient categories with finite Tor amplitude

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-finite-tor-amplitude`, order 1464 (blueprint: def-weil-finite-tor-amplitude).

Finite coefficients impose finite Tor amplitude in addition to constructibility.
Integral coefficients impose one Tor interval for all positive finite reductions.
At field coefficients the notation is an alias for the bounded constructible category
itself, including its common-stage interpretation at algebraically closed coefficients;
`finiteTorFieldCoefficientCategory` expresses this alias parametrically in that category.
Triangulated closure is supplied by separate statement nodes, not by these definitions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry.Scheme

namespace WeilConjectures

end WeilConjectures
