/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Strictly semistable relative curves

Source: Temkin, *Stable modification of relative curves*, §1.2 and §4.3, Proposition 4.3.1
(blueprint: def-trf-strict-semistable-curve).

## Main definitions

* `AlgebraicGeometry.strictNodalRing`: the standard nodal chart algebra.
* `AlgebraicGeometry.StrictSemistableModel`: the two standard models and their projections.
* `AlgebraicGeometry.StrictSemistableChart`: a chart around a point over an affine base open.
* `AlgebraicGeometry.StrictSemistableCurve`: a finitely presented curve with these charts.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The nodal algebra `A[u,v]/(uv-a)` used in a strict semistable chart.
Source: Temkin, *Stable modification of relative curves*, §4.3
(blueprint: def-trf-strict-semistable-curve). -/
noncomputable def strictNodalRing (A : CommRingCat.{u}) (a : A) : Type u :=
  (MvPolynomial (Fin 2) A) ⧸
    Ideal.span ({MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a} :
      Set (MvPolynomial (Fin 2) A))

/-- The quotient commutative ring structure of the nodal chart.
Source: Temkin, §4.3 (blueprint: def-trf-strict-semistable-curve). -/
noncomputable instance strictNodalRingCommRing (A : CommRingCat.{u}) (a : A) :
    CommRing (strictNodalRing A a) :=
  Ideal.Quotient.commRing _

/-- A strict semistable chart model is either `Spec A[t]` or `Spec A[u,v]/(uv-a)`.
Source: Temkin, *Stable modification of relative curves*, §4.3
(blueprint: def-trf-strict-semistable-curve). -/
inductive StrictSemistableModel (A : CommRingCat.{u}) : Type u
  | polynomial
  | nodal (a : A)

/-- The affine scheme of a standard chart.
Source: Temkin, §4.3 (blueprint: def-trf-strict-semistable-curve). -/
noncomputable def StrictSemistableModel.scheme {A : CommRingCat.{u}}
    (M : StrictSemistableModel A) : Scheme.{u} :=
  match M with
  | .polynomial => Spec (.of (Polynomial A))
  | .nodal a => Spec (.of (strictNodalRing A a))

/-- The standard chart projection induced by the coefficient ring homomorphism.
Source: Temkin, §4.3 (blueprint: def-trf-strict-semistable-curve). -/
noncomputable def StrictSemistableModel.baseMap {A : CommRingCat.{u}}
    (M : StrictSemistableModel A) : M.scheme ⟶ Spec A :=
  match M with
  | .polynomial =>
      Spec.map (CommRingCat.ofHom (Polynomial.C : (A : Type u) →+* Polynomial A))
  | .nodal _a =>
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk _).comp (MvPolynomial.C : (A : Type u) →+* MvPolynomial (Fin 2) A)))

/-- A local strict semistable chart around a point of a relative curve.
Source: Temkin, *Stable modification of relative curves*, §4.3
(blueprint: def-trf-strict-semistable-curve). -/
structure StrictSemistableChart {T Y : Scheme.{u}} (f : Y ⟶ T) (y : Y) where
  base : T.Opens
  base_affine : IsAffineOpen base
  A : CommRingCat.{u}
  base_iso : Spec A ≅ base.toScheme
  neighbourhood : Y.Opens
  point_mem : y ∈ neighbourhood
  over_base : neighbourhood ≤ f ⁻¹ᵁ base
  model : StrictSemistableModel A
  map : neighbourhood.toScheme ⟶ model.scheme
  etale : Etale map
  over : map ≫ model.baseMap ≫ base_iso.hom ≫ base.ι =
    neighbourhood.ι ≫ f

/-- A strictly semistable `T`-curve, without separatedness or properness assumptions.
Source: Temkin, *Stable modification of relative curves*, §1.2 and §4.3, Proposition 4.3.1
(blueprint: def-trf-strict-semistable-curve). -/
structure StrictSemistableCurve (T : Scheme.{u}) where
  Y : Scheme.{u}
  structureMap : Y ⟶ T
  flat : Flat structureMap
  locally_finite_presentation : LocallyOfFinitePresentation structureMap
  quasi_compact : QuasiCompact structureMap
  quasi_separated : QuasiSeparated structureMap
  pure_relative_dimension_one : ∀ t : T,
    (structureMap.fiber t).IsPureDimension 1
  chart : ∀ y : Y, Nonempty (StrictSemistableChart structureMap y)

end AlgebraicGeometry
