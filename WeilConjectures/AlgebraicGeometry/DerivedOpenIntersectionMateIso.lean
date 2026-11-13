/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenIntersectionIsoDetection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # The restriction mate for the intersection of two opens

Source: Stacks Project, Tags 08FE and 08DG.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem open_counit_isIso
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι) :
    IsIso adj.counit := by
  let G := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : schemeOpenRestriction X U ⊣ G :=
    (Scheme.Modules.restrictAdjunction U.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv U).symm
  have : G.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : G.Full :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : G.Faithful :=
    (Scheme.Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful adj

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
-- The transported overlap restriction requires additional instance search.
-- The derived composition comparison requires a larger elaboration budget.
/-- Restricting the canonical mate from the direct image on P to the direct image
on O ∩ P gives an isomorphism on O (Stacks, Tags 08FE and 08DG). -/
theorem derived_open_intersection_mate_isIso
    (X : Scheme.{u}) (O P W : X.Opens) (hW : W = O ⊓ P) (i : W ⟶ P)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings O.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (adjP : (schemeOpenRestriction X P).mapDerivedCategory ⊣ schemeDerivedDirectImage P.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι)
    (B : schemeDerivedCategory P.toScheme) :
    let sP := (schemeOpenOverlapRestriction X i).mapDerivedCategory;
    let eP := schemeDerivedOpenRestrictionCompIso X i;
    IsIso ((schemeOpenRestriction X O).mapDerivedCategory.map
      ((adjW.homEquiv ((schemeDerivedDirectImage P.ι).obj B) (sP.obj B))
        (eP.inv.app _ ≫ sP.map (adjP.counit.app B)))) := by
  dsimp only
  have := open_counit_isIso X P adjP
  have := open_counit_isIso X W adjW
  let sP := (schemeOpenOverlapRestriction X i).mapDerivedCategory
  let eP := schemeDerivedOpenRestrictionCompIso X i
  let f := (adjW.homEquiv ((schemeDerivedDirectImage P.ι).obj B) (sP.obj B))
    (eP.inv.app _ ≫ sP.map (adjP.counit.app B))
  have hcomp : (schemeOpenRestriction X W).mapDerivedCategory.map f ≫
      adjW.counit.app (sP.obj B) =
        eP.inv.app _ ≫ sP.map (adjP.counit.app B) := by
    exact (adjW.homEquiv _ _).symm_apply_apply _
  have : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map f ≫
      adjW.counit.app (sP.obj B)) := by
    rw [hcomp]
    infer_instance
  have hf : IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map f) :=
    IsIso.of_isIso_comp_right _ (adjW.counit.app (sP.obj B))
  exact derived_open_intersection_isIso_of_restriction X O P W hW B (sP.obj B) f hf

end AlgebraicGeometry
