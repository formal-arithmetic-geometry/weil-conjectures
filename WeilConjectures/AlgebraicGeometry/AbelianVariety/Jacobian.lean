/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# The Jacobian of a curve

A *Jacobian* of a smooth projective geometrically integral curve `C` over `K` is an abelian
variety `J` over `K` of dimension the genus of `C`, together with an isomorphism of group-valued
functors between the degree-zero relative Picard functor `Pic⁰_{C/K}` and the functor of points
of `J`.

## Implementation notes

The degree-zero relative Picard functor is `AlgebraicGeometry.picardFunctorDegree f 0`, the fppf
sheafification of the presheaf of classes of fibrewise degree zero. It takes values in
`Type (u + 1)`, so the functor of points of `J` is lifted to that universe by
`CategoryTheory.uliftFunctor`. Its group law is induced by the tensor product of invertible
modules, and that the isomorphism is one of group-valued functors is the predicate
`AlgebraicGeometry.IsPicardZeroMul`: the map from classes of degree zero to points of `J` turns
the tensor product into the group law of `J`.

The existence of a Jacobian over a separably closed field is
`AlgebraicGeometry.exists_jacobian`, and over a general field
`AlgebraicGeometry.exists_commGrpObj_representableBy_picardFunctorDegree`.

## Main definitions

- `AlgebraicGeometry.IsJacobian`: the property of being a Jacobian of a curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `sk-def-av-jacobian`: The Jacobian

Let `C` be a smooth projective geometrically integral curve over a field `K`, of genus `g`. A
*Jacobian of `C`* is a pair `(J, φ)` consisting of an abelian variety `J` over `K` of dimension
`g` together with an isomorphism of group-valued functors `φ : Pic⁰_{C/K} ≅ h_J` on `(Sch/K)`;
that is, `J` represents the degree-zero relative Picard functor.

The functor `Pic⁰_{C/K}` is `AlgebraicGeometry.picardFunctorDegree f 0`, with values in
`Type (u + 1)`, and `h_J` is the functor of points `yoneda.obj J`, lifted to `Type (u + 1)`. The
isomorphism respects the group laws: for every `K`-scheme `T`, the map sending a class of
fibrewise degree zero in `Pic (C_T)` to the point of `J` that `φ` attaches to it turns the tensor
product of invertible modules into the group law of `J` (`AlgebraicGeometry.IsPicardZeroMul`).

Representability is stated as the existence of `φ` rather than as a chosen isomorphism, so that
`IsJacobian` is a `Prop`; the data of `φ` is recovered by choice.

The hypotheses on `f` are those of a geometrically integral smooth proper curve; a smooth
projective curve in the sense of `AlgebraicGeometry.IsSmoothProjectiveCurve` satisfies them,
since it is a connected curve (`AlgebraicGeometry.IsIntegralCurve.isConnectedCurve`) and proper
(`AlgebraicGeometry.IsHProjective.isProper`). The genus is `f.genus = dim_K Γ(C, Ω¹_{C/K})`,
which agrees with `dim_K H¹(C, 𝒪_C)` (`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`).

(blueprint: `def-sc-jacobian`) -/
class IsJacobian (f : C ⟶ Spec (.of K)) [IsCurve f] [Smooth f] [IsProper f]
    [GeometricallyIntegral f] (J : Over (Spec (.of K))) [GrpObj J] : Prop
    extends IsAbelianVariety J where
  /-- The dimension of a Jacobian of `C` is the genus of `C`. -/
  dim_eq : IsAbelianVariety.dim J = f.genus
  /-- A Jacobian of `C` represents the degree-zero relative Picard functor of `C`, by an
  isomorphism of group-valued functors. -/
  represents : ∃ φ : (picardFunctorDegree f 0).obj ≅ yoneda.obj J ⋙ uliftFunctor.{u + 1},
    IsPicardZeroMul f ((Functor.RepresentableBy.equivUliftYonedaIso _ J).symm φ.symm)

end AlgebraicGeometry
