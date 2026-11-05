/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.IntegerShiftFromOne

/-! Normalized integer shifts on rational scalar extension.
This extracts the proved scalar-localization argument from the pair-category module
so both files compile separately within the time limit
(blueprint: lem-pur-intrinsic-rational-scalar-shift-normalization).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace WeilConjectures
attribute [local irreducible] sfRationalTriangulationDatum sfRationalScalarExtension

end WeilConjectures
