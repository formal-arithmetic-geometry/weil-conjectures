/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFamily
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-unit-coordinates). -/

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

/-- The coefficient unit in degree zero, with its existing module structure.
Source: constant coefficients (blueprint: def-pur-transport-unit-coordinates). -/
abbrev unit (c : Coefficient ell) (X : Scheme.{u}) : c.derived ell X :=
  (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)

/-- The canonical evaluation J_f(1)=Lambda(d)[2d], using the inverse-image unit.
Source: Cartesian coefficients (blueprint: def-pur-transport-unit-coordinates). -/
def sourceUnit (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (c.smoothSource ell f d).obj (unit ell c Y) ≅ c.derivedLine ell X d :=
  tensorIso
    (((CondensedRing.upperStar (c.obj ell) f).singleFunctorCompLeftDerivedFunctorIso).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) f)).symm ≪≫
      DerivedCategory.singleFunctorObjUnitIso _) (Iso.refl _) ≪≫ λ_ _

end AlgebraicGeometry.ProEtale.PurityTransport
