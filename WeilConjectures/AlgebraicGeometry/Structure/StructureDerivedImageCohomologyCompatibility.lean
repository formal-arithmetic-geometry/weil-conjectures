/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Module.ModuleCohomologyExtHMap

/-! The module-to-abelian comparison for structure modules.

Source: Stacks Project, Tags 03FD and 01F7. -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The fixed injective-resolution comparison between degree-one structure-module
cohomology and abelian sheaf cohomology of the structure sheaf. -/
noncomputable def structureModuleAbelianEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{v}) :
    (RingedSpace.moduleCohomology Y.toRingedSpace 1).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≃+
      Sheaf.H (structureSheafAb Y) 1 :=
  Modules.moduleCohomologyExtResolutionEquiv Y (SheafOfModules.unit Y.ringCatSheaf) 1

-- Transporting the fixed resolution comparison through the module aliases is expensive.
/-- The fixed resolution comparison `structureModuleAbelianEquiv` respects every structure
h-map.
Source: Stacks Project, Tags 03FD (comparison) and 01FB (coefficient factorization). -/
theorem structure_module_abelian_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{v}} (g : Y ⟶ X) (x :
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) :
    structureModuleAbelianEquiv Y (Modules.moduleCohomologyFMap g
        (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1 x) =
      structureSheafCohomologyPullback g 1 (structureModuleAbelianEquiv X x) := by
  classical
  exact Modules.moduleCohomologyExtResolutionEquiv_hmap g
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1 x

end AlgebraicGeometry.Scheme
