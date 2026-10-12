/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit

/-!
# Torsion cohomological dimension of curves and of one-variable function fields

A separated scheme of finite type and dimension at most one over an algebraically closed field
has torsion étale cohomological dimension at most two, and at most one if it is affine
(`AlgebraicGeometry.IsCurve.hasTorsionCohomologicalDimensionLE`, blueprint
`lem-sc-arbitrary-curve-cd`). Consequently the rational function field `F(x)` in one variable over
a separably closed field `F` has torsion cohomological dimension at most one
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_one_ratFunc`, blueprint
`lem-sc-one-variable-field-cd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-sc-arbitrary-curve-cd`: The torsion bound on an arbitrary algebraic curve.

Let `X` be a separated scheme of finite type and of dimension at most one over an algebraically
closed field `k` (that is, `X ⟶ Spec k` is an `AlgebraicGeometry.IsCurve`). Then
`cd_tor(X) ≤ 2`, and `cd_tor(X) ≤ 1` if `X` is affine. -/
theorem IsCurve.hasTorsionCohomologicalDimensionLE {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] :
    X.HasTorsionCohomologicalDimensionLE 2 ∧
      (IsAffine X → X.HasTorsionCohomologicalDimensionLE 1) :=
  ⟨fun F hF q hq ↦ subsingleton_sheafH_of_three_le f F hF q hq,
    fun _ F hF q hq ↦ subsingleton_sheafH_of_two_le_of_isAffine f F hF q hq⟩

/-- Blueprint `lem-sc-one-variable-field-cd`: One-variable fields over a separably closed field.

If `F` is a separably closed field, then the rational function field `F(x)` has torsion
cohomological dimension at most one: `cd_tor(Spec F(x)) ≤ 1`. -/
theorem Scheme.hasTorsionCohomologicalDimensionLE_one_ratFunc (F : Type u) [Field F]
    [IsSepClosed F] : (Spec (.of (RatFunc F))).HasTorsionCohomologicalDimensionLE 1 :=
  sorry

end AlgebraicGeometry
