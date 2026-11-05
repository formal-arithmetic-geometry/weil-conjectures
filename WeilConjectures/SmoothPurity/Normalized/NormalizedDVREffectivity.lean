/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRRoosFiniteReduction
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatReductionModel
import Mathlib.Algebra.Homology.Functor

/-! # Effectivity of normalized DVR towers

Source: Weil conjectures blueprint, sec-six-functors, sk-prop-sf-biduality-general,
order 2132 (blueprint: lem-coef-normalized-dvr-effectivity).

The derived limit is specified by its Roos triangle on actual derived evaluations.
Comparisons are adjoints of the specified limit projections. Coherence is an equality
in the finite-coefficient derived category, including both identity and longer quotient
maps. No constructibility, boundedness, or Tor-amplitude hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local instance 4000] normalizedDVREffectivityLocal1
attribute [local instance] normalizedDVREffectivityLocal2
attribute [local instance] normalizedDVREffectivityLocal3

attribute [local irreducible] normalizedDVRIntegralAdjunction
  scalarReductionExtension scalarReductionDerivedExtension scalarReductionCounit
  normalizedDVRKFlatComparison

end WeilConjectures
