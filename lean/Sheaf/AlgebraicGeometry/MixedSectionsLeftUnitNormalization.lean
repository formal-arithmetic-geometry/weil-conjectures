/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate

/-! # Left path of the normalized mixed Leray unit diagram
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-left-unit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

set_option maxHeartbeats 800000 in
-- The statement expands sheaf, scalar, and localization instances.
/-- The left path becomes the iterated scalar-factor path before any unit cancellation.
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W; the pinned-unit calculation
in lem-sc-mixed-sections-composition-kinjective.
(blueprint: lem-sc-mixed-sections-left-unit-normalization).

Proof: Expand p using the normalized direct-image composition equation:
unit_Dfg followed by e.inv equals unit_Dg at Df(K), followed by RDg(unit_Df).
Naturality of c_g at unit_Df moves RDg(unit_Df) across c_g. Apply the mixed Leray
unit equation for g at Df(K). The two remaining maps inside Sg combine, by
functoriality, with the global-sections unit on Y. Apply the mixed Leray unit
equation for f at K. Distribute Sg over this composite to obtain b. The underived
Leray comparisons are identity on sections; their homotopy composition maps
cancel with their inverses. No unit is canceled, and I need not be K-injective.
For identity maps, zero complexes, and empty schemes the same equations hold;
no nonemptiness, boundedness, flatness, or preservation of K-injectivity is used.
The sheaf and module localization universes remain independent. -/
theorem mixedSections_left_unit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let F := DerivedCategory.Qh.obj K
    let Df := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
    let HX := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let HY := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let HZ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
    let Sf := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom
    let Sg := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Z.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings Y.toRingedSpace).obj.obj (op ⊤)) g.appTop.hom
    let e := schemeNormalizedDirectImageCompIso f g
    let p := HZ.rightDerivedFunctorUnit.app ((Dfg.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Z).map (Dfg.rightDerivedFunctorUnit.app K) ≫
      (schemeDerivedGlobalSections Z).map (e.inv.app F)
    let b := Sg.mapDerivedCategoryFactorsh.inv.app
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((Df.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        (Sf.mapDerivedCategoryFactorsh.inv.app ((HX.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalScalarRestriction f).map (HX.rightDerivedFunctorUnit.app K))
    p ≫ (mixedGlobalSectionsDirectImageIso g).hom.app
        ((schemeDerivedDirectImage f).obj F) ≫
      (schemeGlobalScalarRestriction g).map
        ((mixedGlobalSectionsDirectImageIso f).hom.app F) = b := by sorry

end AlgebraicGeometry
