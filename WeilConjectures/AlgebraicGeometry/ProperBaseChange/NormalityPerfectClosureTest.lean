/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.ProperBaseChange.NormalAlgebraSeparableScalarExtension
import WeilConjectures.RingTheory.ProperBaseChange.NormalRingFieldExtensionDescent

/-!
# Testing geometric normality over a perfect purely inseparable extension

Source: Stacks Project, Varieties, Tag 038O, equivalence (2) and (6), and Algebra,
Tag 046W, uniqueness of the perfect closure
(blueprint: lem-weil-pbc-normality-perfect-closure-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- This common-overfield proof uses only perfectness; retain the assigned signature.

end AlgebraicGeometry
