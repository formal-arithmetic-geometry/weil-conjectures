module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.GlobalDerivedHom

@[expose] public section

universe u w wA wPt
open CategoryTheory Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Transport of the direct-image unit along the global-sections point comparison.
Source: Stacks Project, Cohomology, Tags 079W and 0D5T; Duality, Tag 0B6I.
(blueprint: new-global-sections-point-unit-transport).

The equivalence between module sheaves on the global-sections point and modules over
its global ring identifies direct image along the point map with global sections.
The comparison of right-derived functors is compatible with the units.  Conjugating
the invertible point unit by these comparison isomorphisms therefore gives an
invertible global-sections unit.  This is the categorical transport step in the
proof of global-sections acyclicity.
-/
theorem globalSections_unit_isIso_of_point_unit
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))]
    [HasDerivedCategory.{wPt}
      (SheafOfModules.{u} (moduleRings (globalSectionsPoint Y)))]
    (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (h : IsIso
      ((RingedSpace.moduleDirectImage (toGlobalSectionsPoint Y)).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    IsIso ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  sorry

end AlgebraicGeometry
