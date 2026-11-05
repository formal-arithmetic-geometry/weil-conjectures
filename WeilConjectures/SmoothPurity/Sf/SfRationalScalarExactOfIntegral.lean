/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi

/-! # Exactness of normalized rational scalar extension from an integral model

This is the rational descent step of the intrinsic transition exactness argument
(blueprint: lem-route-rational-transition-exact-of-integral).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Pretriangulated

namespace WeilConjectures

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum
  sfRationalScalarExtension ScalarLocalization.composition

end WeilConjectures
