/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.PoincareDuality.PrincipalDerivedTensorCone
import WeilConjectures.PoincareDuality.Point.PointReductionCoefficientRing

/-! The cone comparison for point-section reduction.

The coefficient calculation is isolated from the transport along a chosen model of sections.
This avoids restating the whole target as an intermediate theorem: the core lemma below has
an arbitrary module complex as input, while the exported clause only transports it along the
supplied isomorphism.  The coefficient calculation is the two-term free resolution of the
principal quotient; its small torsion-freeness input is recorded separately.
(blueprint: lem-pod-point-sections-derived-reduction-cone) -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
