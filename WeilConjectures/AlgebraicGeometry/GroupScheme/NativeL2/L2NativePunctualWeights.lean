/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Punctual weights on native condensed Weil modules

Source: latest blueprint, def-weil-punctual-weights, closed-point eigenvalue and
finite-filtration clauses (blueprint: def-weil-punctual-weights).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The existing Weil-module category at the geometric Frobenius.
Source: latest blueprint, Weil-structure clause (blueprint: def-weil-punctual-weights). -/
abbrev WeilModule := condensedWeilModules (Profinite.padicAlgClRingObj l)
  (D.geometricFrobenius X₀).hom

/-- The canonical local operator on actual sections at the indicated geometric lift.
Source: latest blueprint, F_y (blueprint: def-weil-punctual-weights). -/
@[irreducible] def closedOperator (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :=
  operator l D (D.geometricFrobenius X₀).hom M.carrier M.str
    (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi)

/-- Every closed-point eigenvalue has the prescribed absolute value, for every lift.
The scalar lift changes only the universe, and is removed before applying iota.
Source: latest blueprint, displayed purity equation (blueprint: def-weil-punctual-weights). -/
def Pure (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
      ‖iota α.down‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)

end WeilConjectures.NativeL2
