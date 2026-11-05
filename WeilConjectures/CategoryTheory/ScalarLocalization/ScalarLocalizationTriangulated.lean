/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Triangulation of scalar localization

Source: Stacks Project, Derived Categories, Tags 05R2 and 05R6, applied to the scalar
localization in the blueprint `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-triangulated).
-/

@[expose] public section

universe r u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory
namespace ScalarLocalization

end ScalarLocalization
end CategoryTheory
