/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRAdicConeModel

/-! # Finite reductions of a normalized DVR Roos limit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
attribute [local instance] normalizedDVRRoosFiniteReductionLocal1
attribute [local instance] normalizedDVRRoosFiniteReductionLocal3
attribute [local instance] normalizedDVRRoosFiniteReductionLocal4

end WeilConjectures
