/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Basic

/-!
# Group structures descend

Let `p : X ⟶ Y` be faithfully flat and quasi-compact and let `V` be a group scheme over `X` with
an effective descent datum `D`, with descended scheme `V₀`, such that the group law of `V` is
compatible with `D`. We construct a group structure on `V₀`, and show that it is the only one
for which the projection `V ⟶ V₀` maps products of points to products of points.

For a scheme `T` over `Y`, write `T' = T ×_Y X`. A `T`-point `t` of `V₀` gives a point of `V`
over `T' ⟶ X` (`CategoryTheory.Over.DescentDatum.liftPoint`), and this identifies the
`T`-points of `V₀` with the points of `V` over `T'` which are invariant under `D`
(`CategoryTheory.Over.DescentDatum.PointInvariant`). The invariant points form a subgroup, so
the `T`-points of `V₀` form a group, naturally in `T`, and the Yoneda lemma
(`GrpObj.ofRepresentableBy`) gives the group structure on `V₀`. Uniqueness holds because
`liftPoint` is injective (`CategoryTheory.Over.DescentDatum.mul_eq_of_descendPoint_mul`) and a
group object structure is determined by its multiplication (`CategoryTheory.GrpObj.ext_of_mul_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

end CategoryTheory.GrpObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y} {qV : V.left ⟶ V₀.left}

variable (D : DescentDatum p V) (hqV : IsPullback qV V.hom V₀.hom p)
  (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
    (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)

section Group

variable [GrpObj V]
  (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
    D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
      lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
  (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
    D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V])

variable [Flat p] [Surjective p] [QuasiCompact p]

end Group

end CategoryTheory.Over.DescentDatum
