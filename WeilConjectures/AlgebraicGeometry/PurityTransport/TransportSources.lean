/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-source-comparisons). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The proper/open composition model is the actual composite compactification.
Source: compact-support composition (blueprint: def-pur-transport-source-comparisons). -/
def compositeCompactification {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i)) :
    Compactification (f ≫ g) where
  Z := cr.obj.obj.Z
  i := cf.i ≫ cr.obj.obj.i
  g := cr.obj.obj.g ≫ cg.g
  isProper := inferInstance
  isOpenImmersion := inferInstance
  comm := calc
    f ≫ g = (cf.i ≫ cf.g) ≫ g := congrArg (· ≫ g) cf.comm
    _ = cf.i ≫ ((cf.g ≫ cg.i) ≫ cg.g) :=
      (congrArg (fun h ↦ (cf.i ≫ cf.g) ≫ h) cg.comm).trans (by simp)
    _ = cf.i ≫ ((cr.obj.obj.i ≫ cr.obj.obj.g) ≫ cg.g) :=
      congrArg (fun h ↦ cf.i ≫ (h ≫ cg.g)) cr.obj.obj.comm
    _ = (cf.i ≫ cr.obj.obj.i) ≫ (cr.obj.obj.g ≫ cg.g) := by simp

end AlgebraicGeometry.ProEtale.PurityTransport
