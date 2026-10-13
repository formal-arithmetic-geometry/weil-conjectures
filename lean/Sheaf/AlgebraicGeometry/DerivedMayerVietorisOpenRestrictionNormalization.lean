/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Restriction normalization by derived units

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-derived-mayer-vietoris-open-restriction-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

variable (X Y : Scheme.{u}) (h : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ T : X.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  [∀ T : Y.Opens, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
  (U : Y.Opens)

attribute [local instance 2000] schemeMVModuleAbelian

/-- The canonical restriction comparison is the derivation of the sectionwise
restriction identification, with its exact-source and exact-target factors.
Source: Stacks Tag 08FE; Tag 0D5T for the composition factors.
Proof: unfold the four factors of schemeMVOpenRestrictionComparison. For the first
factor use the determining equation of rightDerivedFunctorCompMapDerivedCategoryIso;
for the second use rightDerivedNatTrans_fac; for the third use the determining
rightDerivedUnique equation of rightDerivedFunctorCompIso. For the fourth use
rightDerivedFunctorIsoMapDerivedCategory_hom_fac. The intermediate units cancel,
and the mapHomotopyCategory composition factors identify the remaining underived
natural transformation with schemeMVUnderivedOpenRestriction. This proves the
formula for every homotopy object, not only a K-injective one. Empty and full opens
are included because the equation is a factorization of natural transformations.
(blueprint: lem-pc-derived-mayer-vietoris-open-restriction-normalization). -/
theorem schemeMVOpenRestriction_unit_normalization
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
    let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
    let LY := schemeOpenRestriction Y U
    LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
        (schemeMVOpenRestrictionComparison h U).hom.app (DerivedCategory.Qh.obj K) ≫
        G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.hom.app K) =
      LY.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((schemeMVHomotopyOpenRestriction h U).hom.app K) ≫
        G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
      := by sorry

end AlgebraicGeometry
