/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel

/-! # The underived open counit square

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-underived-open-counit-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry


/-- The sectionwise comparison square respects the two underived open counits,
after passage to the homotopy category.
Source: Stacks Tags 08FE and 08BV.
Proof: on an open W of U, both composites are the restriction identification of
sections of I over g inverse image W. Use restrictAdjunction_counit_app_app for
the two counits and the sectionwise formulas for pushforwardComp and
pushforwardCongr. Transport along overFunctorEquiv, which is the identification
used to define schemeOpenModuleAdjunction and schemeMVUnderivedOpenRestriction.
The equalities are natural in I and commute with its differentials. Apply the
termwise functors, then the homotopy quotient; the quotient counit formula
mapHomotopyCategory_counit_app_quotient identifies their counits. Every homotopy
object is a quotient of a complex, so this gives the displayed equation for all K.
For the empty open this is the unique map between zero objects; for the full open
it is the same sectionwise identity. No derived comparison occurs here.
(blueprint: lem-pc-mayer-vietoris-underived-open-counit-square). -/
theorem schemeMVUnderivedOpenCounit_square
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
    let LY := schemeOpenRestriction Y U
    (LY.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        (schemeMVHomotopyOpenAdjunction Y U).counit.app
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (schemeMVHomotopyOpenRestriction h U).hom.app
          ((RX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((schemeMVHomotopyOpenAdjunction X (h ⁻¹ᵁ U)).counit.app K) := by sorry

end AlgebraicGeometry
