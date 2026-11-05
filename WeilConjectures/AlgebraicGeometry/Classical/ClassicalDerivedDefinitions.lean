/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Classical module and derived predicates

Source: the Weil conjectures blueprint, `sk-def-pe-classical-definition`
(blueprint: sk-def-pe-classical-definition).

The predicates below use the canonical continuity maps on affine pro-étale
presentations, in the coefficient category used by the comparison adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

end
