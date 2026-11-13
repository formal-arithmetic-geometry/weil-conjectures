/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
import WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.GlobalSectionsPointUnitTransport

/-!
# Global-sections acyclicity of a direct image of a K-injective

Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I.
-/

@[expose] public section

universe u w wA
open CategoryTheory Opposite
set_option autoImplicit false

namespace AlgebraicGeometry

/-- Direct image of a K-injective complex is acyclic for subsequent global sections.
No preservation of K-injectivity by direct image is asserted.
Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I. -/
theorem isIso_directImage_globalSections_unit_on_kInjective
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    IsIso ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  let _ : HasDerivedCategory (SheafOfModules.{u} (moduleRings (globalSectionsPoint Y))) :=
    HasDerivedCategory.standard _
  apply globalSections_unit_isIso_of_point_unit f I
  exact RingedSpace.isIso_moduleDirectImage_unit_on_kInjective
    f.toLRSHom.toShHom (toGlobalSectionsPoint Y) I

end AlgebraicGeometry
