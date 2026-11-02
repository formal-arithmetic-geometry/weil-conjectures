/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.Complex.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs

/-! # Reality on actual condensed Weil modules

Source: latest blueprint, `def-wf-iota-real.md`, local characteristic factor and
reality paragraphs (blueprint: def-zl-condensed-weil-reality).

The formulas below apply directly to ordinary modules over the pulled-back condensed
coefficient ring.  No finite-stage or common-stage presentation is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeCondensedWeil

open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The reverse characteristic polynomial in a finite basis of the actual scalar fibre.
Source: latest blueprint, `def-wf-iota-real.md`, basis formula
(blueprint: def-zl-condensed-weil-reality). -/
def localFactorInBasis
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (n : ℕ)
    (b : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D M.carrier (localClosedPoint D X₀ x i hi))) :
    Polynomial (ULift.{u + 1} (PadicAlgCl l)) :=
  (LinearMap.toMatrix b b
    (NativeCondensedModule.operator l D (D.geometricFrobenius X₀).hom M.carrier M.str
      (localClosedPoint D X₀ x i hi)
      (localClosedPointDegree D X₀ x - 1)
      (localClosedPoint_return D X₀ x i hi)).hom).charpoly.reverse

/-- Coefficientwise reality of every actual local factor after a chosen embedding.
The predicate is defined on the ambient actual Weil-module category; finite-dimensionality
is only required when a basis is supplied.
Source: latest blueprint, `def-wf-iota-real.md`, reality paragraph
(blueprint: def-zl-condensed-weil-reality). -/
def Real
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (iota : PadicAlgCl l →+* ℂ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (n : ℕ)
    (b : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D M.carrier (localClosedPoint D X₀ x i hi)))
    (j : ℕ),
    (iota (ULift.down ((localFactorInBasis D l X₀ M x i hi n b).coeff j))).im = 0

end WeilConjectures.NativeCondensedWeil
