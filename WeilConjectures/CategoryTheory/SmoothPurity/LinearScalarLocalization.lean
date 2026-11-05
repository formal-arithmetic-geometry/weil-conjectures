/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Category laws for raw scalar localization

Source: the Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi` (blueprint: lem-weil-linear-scalar-localization-category).
The scalar-first tensor order is the convention of `LinearMap.baseChange`.
`ULift.{0} C` is only a wrapper for the unchanged objects, with no new objects adjoined.
-/

@[expose] public section

set_option linter.unusedVariables false

universe r u v

open CategoryTheory TensorProduct

namespace CategoryTheory

namespace LinearScalarConstruction

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)

-- This is the explicit construction above, not ScalarLocalization.composition, whose
-- definition uses exists_linear_scalarLocalization_category and cannot be imported here.

end LinearScalarConstruction

open LinearScalarConstruction

end CategoryTheory
