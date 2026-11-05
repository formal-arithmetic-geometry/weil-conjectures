/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.PrincipalReductionComparison
import WeilConjectures.PoincareDuality.Point.PointPrincipalReductionCoefficients
import WeilConjectures.PoincareDuality.Point.PointReductionCoefficientRing
import WeilConjectures.PoincareDuality.ScalarReductionCochainComparison
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Point sections commute with derived principal reduction

The coefficient sequence, flat-resolution comparison and localization descent follow
steps 1--10 of the original proof. No point-reduction normalization theorem is used.
(blueprint: lem-pod-point-sections-derived-reduction-iso) -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
