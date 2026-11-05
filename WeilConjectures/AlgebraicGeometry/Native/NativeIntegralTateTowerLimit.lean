/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateFiniteRepresentation
import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Inverse image preserves the native integral Tate tower limit

Source: the Integral twist paragraph of the blueprint proof of
`sk-prop-sfb-cartesian-coefficients-twists`.
(blueprint: lem-pur-native-integral-tate-tower-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
