/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility
import WeilConjectures.WeilSheaf.Native.NativeCoefficientTensorComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Internal Hom under the native geometric realization

Source: current blueprint, `lem-fix-weil-operations.proof.md`, internal-Hom paragraph;
the coefficient realization and native closed-forgetful comparison.
(blueprint: lem-sf-native-geometric-hom-comparison).

This is an ambient derived-object comparison. It asserts no constructibility,
boundedness, dualizing-object identification, or biduality.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

end AlgebraicGeometry.ProEtaleWeilSheaf
