/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquareSection

/-! # The ordinary open counit square

## References

* [Stacks, Tags 08FE and 08BV]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry


/-- Counit compatibility for the fixed comparisons on ordinary sheaves of modules
(Stacks, Tags 08FE and 08BV). -/
theorem schemeMVOrdinaryOpenCounit_square
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) :
    (schemeOpenRestriction Y U).map
        ((schemeMVUnderivedOpenComposition h U).hom.app M) ≫
        (schemeOpenModuleAdjunction Y U).counit.app
          ((RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).obj M) =
      (schemeMVUnderivedOpenRestriction h U).hom.app
          ((RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj M) ≫
        (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).map
          ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).counit.app M) := by
  ext W
  exact congrFun (congrArg (fun q => q.hom)
    (schemeMVOrdinaryOpenCounit_square_app X Y h U M W)) _
end AlgebraicGeometry
