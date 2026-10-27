/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent

/-! # Additivity of normalized degree-one chart fractions

Source: Stacks Project, Constructions, Tag 01NR.
(blueprint: lem-trf-relative-proj-twist-chart-fraction-add).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The normalized homogeneous degree-one chart fraction is additive in its numerator.

The proof is the pointwise localization calculation for `a/1 + b/1 = (a+b)/1`.
It uses `Proj.val_unitToTwist_app_apply` to evaluate each normalized fraction and
then the additive law in the localization at the homogeneous prime. The calculation
is independent of the relative-Proj descent object; it is the local fraction step
used when constructing the additive transition maps.

Source: Stacks Project, Constructions, Tag 01NR, the homogeneous fraction formula in
the proof of `lemma-glue-relative-proj-twists`.
(blueprint: lem-trf-relative-proj-twist-chart-fraction-add).
-/
theorem twistChartFraction_add (U : S.affineOpens) (a b : A.grading U 1) :
    A.twistChartFraction U (a + b) =
      A.twistChartFraction U a + A.twistChartFraction U b := by
  sorry

end AlgebraicGeometry.Scheme.GradedAlgebraData
