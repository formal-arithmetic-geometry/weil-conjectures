/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EulerProductAux
public import WeilConjectures.PointCount
public import WeilConjectures.ZetaCounting.EulerProducts

@[expose] public section

/-!
# The Euler product expansion of the zeta function

For a scheme `X` of finite type over a finite field `k`, given by a structure morphism
`f : X ⟶ Spec k`, we prove the Euler product expansion of its zeta function:

`Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`,

the product running over the closed points of `X` and converging coefficientwise (there
are only finitely many closed points of each degree by
`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`).

This is the special case of `PowerSeries.countingZetaSeries_eq_tprod` for the degree
function `x ↦ [κ(x) : k]` on the closed points of `X`: the point counting formula
`AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum` is exactly its counting hypothesis, and
`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le` its local finiteness
hypothesis.

Substituting `t = q ^ (-s)` and comparing factors with `#κ(x) = q ^ deg x` shows that
this is the Euler product defining the zeta function `AlgebraicGeometry.Scheme.zeta` of
`X` as an abstract scheme.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

open scoped PowerSeries.WithPiTopology in
/-- **The Euler product expansion** of the zeta function of a scheme of finite type over
a finite field: `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`, the product running over the closed
points of `X` and converging coefficientwise. -/
theorem Hom.zetaSeries_eq_tprod [Finite k] (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] :
    f.zetaSeries =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ := by
  rw [f.zetaSeries_eq_countingZetaSeries]
  exact PowerSeries.countingZetaSeries_eq_tprod (fun x ↦ f.degreeOver_ne_zero x.2)
    f.finite_setOf_degreeOver_le fun _ hn _ hT ↦ f.pointCount_eq_sum hn hT

end AlgebraicGeometry.Scheme
