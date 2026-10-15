/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback

/-! # Pullback of a zero chart class

Source: Stacks Project, Tags 03CB and 0EYM.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Pullback of the zero chart class is zero.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: lem-sc-cartesian-chart-class-pullback-zero).

Proof: The exact derived inverse-image functor is additive. Its map of zero is zero,
and composing that zero morphism with the source and shift comparisons is zero. -/
theorem cartesianChartClassPullback_zero {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (V : B.Etale) (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    : cartesianChartClassPullback a b a' ha V U r hr K q 0 = 0 := by
  simp only [cartesianChartClassPullback, cartesianChartClassPullbackCore,
    Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

end AlgebraicGeometry.Etale
