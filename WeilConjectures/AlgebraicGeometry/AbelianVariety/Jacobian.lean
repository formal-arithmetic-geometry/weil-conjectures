/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Curve

/-!
# The Jacobian of a curve

A *Jacobian* of a smooth projective geometrically integral curve `C` over `K` is an abelian
variety `J` over `K` of dimension the genus of `C`, together with an isomorphism between the
degree-zero relative Picard functor `Pic⁰_{C/K}` and the functor of points of `J`.

## Implementation notes

The relative Picard functor belongs to the `sec-picard-framework` block of the blueprint and is
not available here, so it enters `AlgebraicGeometry.IsJacobian` as the parameter
`P : (Over (Spec (.of K)))ᵒᵖ ⥤ GrpCat.{u}`. **Nothing in the definition ties `P` to `C`**: the
class says that the abelian variety `J` has dimension `genus C` and represents `P`, and any `P`
whatever may be supplied. It cannot yet be tied to `C` here, because the only degree-zero
Picard group available, `AlgebraicGeometry.Scheme.Hom.picZero`, lives in `Type (u + 1)` (see
`WeilConjectures.AlgebraicGeometry.PicardFunctor`) while `GrpCat.{u}`-valued functors take values
in `Type u`. `IsJacobian` should be restated against the relative Picard functor once
`sec-picard-framework` lands.

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
that is, `J` represents the degree-zero relative Picard functor. Here `J : AbelianVariety K`
already carries its group structure and the properness, smoothness and connectedness of its
underlying scheme `J.toOver`.

The relative Picard functor `Pic⁰_{C/K}` enters as the parameter
`P : (Over (Spec (.of K)))ᵒᵖ ⥤ GrpCat`, which the definition does not relate to `C`; see the
implementation notes of this file. The functor of points of `J` as a group-valued functor is
`CategoryTheory.yonedaGrpObj J.toOver`.

Representability is stated as `Nonempty (P ≅ yonedaGrpObj J)` rather than as a chosen
isomorphism, so that `IsJacobian` is a `Prop`; the data of `φ` is recovered by choice. -/
class IsJacobian (f : C ⟶ Spec (.of K)) [IsCurve f] [Smooth f] [IsProper f]
    [GeometricallyIntegral f] (P : (Over (Spec (.of K)))ᵒᵖ ⥤ GrpCat.{u})
    (J : AbelianVariety K) : Prop where
  /-- The dimension of a Jacobian of `C` is the genus of `C`. -/
  dim_eq : J.dim = f.genus
  /-- A Jacobian of `C` represents the degree-zero relative Picard functor of `C`. -/
  represents : Nonempty (P ≅ CategoryTheory.yonedaGrpObj J.toOver)

end AlgebraicGeometry
