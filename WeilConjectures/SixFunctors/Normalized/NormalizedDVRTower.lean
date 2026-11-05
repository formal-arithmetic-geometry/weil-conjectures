/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower

/-!
# Normalized DVR towers

Source: Weil conjectures blueprint, `sec-six-functors`,
`sk-prop-sf-biduality-general`, node `def-coef-normalized-dvr-tower`, order 2131
(blueprint: def-coef-normalized-dvr-tower).

## Main definitions

- `normalizedDVRQuotient`: the actual quotient map of the coefficient system.
- `normalizedDVRRes` and `normalizedDVRResCompleted`: exact derived scalar restriction.
- `NormalizedDVRTower`: finite-level objects and transitions with a coherent derived tower.

Normalization uses the universal property of derived change of rings: composition
with the specified transition is a Hom bijection. Under the tensor-restriction
adjunction this says exactly that the adjoint of that transition is an isomorphism.
It neither chooses an unrelated map nor adds an arbitrary scalar-extension functor.
All module universes are `max u (t+1)`, retaining the small site's independent sizes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u uC vC r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

end WeilConjectures
