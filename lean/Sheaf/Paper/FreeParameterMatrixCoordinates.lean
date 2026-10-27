/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Sheaf.Paper.FreeParameterEvaluationData
public import Mathlib.Data.Matrix.Basic

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-matrix-coordinates). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Finite free point coefficients, with rank zero allowed.
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-matrix-coordinates). -/
abbrev finiteFreePoint (r : ℕ) : PointModules R :=
  ⨁ fun _ : Fin r ↦ 𝟙_ (PointModules R)

/-- The local regular-module model for a checking basis.
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-matrix-coordinates). -/
abbrev finiteFreeLocal (V : Scheme.{u}) (r : ℕ) : Modules R V :=
  ⨁ fun _ : Fin r ↦ 𝟙_ (Modules R V)

/-- Local matrix entries are arbitrary endomorphisms of the local regular module,
equivalently sections of B on V; there is no origin-at-the-point condition.
Source: Stacks 03EK (blueprint: def-sfb-free-parameter-matrix-coordinates). -/
def localMatrix (V : Scheme.{u}) {r s : ℕ} {M M' : Modules R V}
    (e : M ≅ finiteFreeLocal R V r) (e' : M' ≅ finiteFreeLocal R V s)
    (v : M ⟶ M') : Matrix (Fin s) (Fin r) (End (𝟙_ (Modules R V))) :=
  fun i j ↦ biproduct.ι (fun _ : Fin r ↦ 𝟙_ (Modules R V)) j ≫
    e.inv ≫ v ≫ e'.hom ≫ biproduct.π (fun _ : Fin s ↦ 𝟙_ (Modules R V)) i

/-- A checking coordinate of an exactly pulled-back finite free coefficient model.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-matrix-coordinates). -/
def coordinate (V : Scheme.{u}) (r : ℕ)
    (e : (pointPull R V).obj (finiteFreePoint R r) ≅ finiteFreeLocal R V r)
    (i : Fin r) :
    (pointPullD R V).obj
      ((DerivedCategory.singleFunctor (PointModules R) 0).obj (finiteFreePoint R r)) ⟶
    (DerivedCategory.singleFunctor (Modules R V) 0).obj (𝟙_ (Modules R V)) :=
  ((pointPull R V).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor (Modules R V) 0).map
      (e.hom ≫ biproduct.π (fun _ : Fin r ↦ 𝟙_ (Modules R V)) i)

/-- An arbitrary local linear coefficient map as a derived arrow between the
pulled-back point models; v need not be the pullback of a point-module arrow.
Source: Stacks 08J7 (blueprint: def-sfb-free-parameter-matrix-coordinates). -/
def localCoefficientMap (V : Scheme.{u}) (r s : ℕ)
    (v : (pointPull R V).obj (finiteFreePoint R r) ⟶
      (pointPull R V).obj (finiteFreePoint R s)) :=
  ((pointPull R V).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor (Modules R V) 0).map v ≫
    ((pointPull R V).mapDerivedCategorySingleFunctor 0).inv.app _

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
