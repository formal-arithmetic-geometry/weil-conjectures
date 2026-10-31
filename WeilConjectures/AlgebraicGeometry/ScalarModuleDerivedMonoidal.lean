/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ScalarModuleMonoidalClosed
public import WeilConjectures.AlgebraicGeometry.ScalarModuleBraidedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # The canonical derived tensor existence instance for scalar modules -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme
attribute [local instance] scalarModuleMonoidalClosed scalarModuleBraidedCategory

/-- The existing K-flat derived monoidal structure applies to scalar module categories.
Source: `CategoryTheory.Mod.hasFunctorialFlatResolution` and
`DerivedCategory.hasDerivedMonoidalCategory`.
Supply the pulled-back ring's existing commutativity proof in the symmetric sheaf
presentation. The module flat-resolution theorem then supplies functorial flat resolutions,
and the existing K-flat theorem gives the stated derived tensor existence property.
(blueprint: lem-sbc-scalar-module-derived-monoidal)
-/
theorem scalarModuleHasDerivedMonoidalCategory (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := ModuleRingedComparison.internalModules Λ.X X))
      (HomotopyCategory.quasiIso (ModuleRingedComparison.internalModules Λ.X X)
        (ComplexShape.up ℤ)) := by
  have : Abelian.HasFunctorialFlatResolution
      (ModuleRingedComparison.internalModules Λ.X X) := by
    let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
      (inferInstance :
        SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
    have : IsCommMonObj (condensedRingObj Λ.X X) := by
      with_unfolding_all
        exact isCommMonObj_condensedRingObj Λ.X X
    with_unfolding_all
      exact CategoryTheory.Mod.hasFunctorialFlatResolution
  exact DerivedCategory.hasDerivedMonoidalCategory _

end AlgebraicGeometry.Scheme
