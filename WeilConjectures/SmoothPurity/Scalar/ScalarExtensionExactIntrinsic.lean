/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated

import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Shift.Localization
/-! # Exactness of intrinsic finite scalar extension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-pf-reduction/lem-weil-scalar-extension-exact-triangulated.md`
(blueprint: lem-weil-scalar-extension-exact-triangulated).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u r v

open CategoryTheory

open scoped TensorProduct
open TensorProduct

namespace WeilConjectures

attribute [local irreducible] sfRationalTriangulationDatum

end WeilConjectures
