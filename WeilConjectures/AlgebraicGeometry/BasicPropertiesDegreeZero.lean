/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-! # DegreeZero property of module cohomology maps

## References

* Stacks Project, Tags 01F7 and 01FB
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero property of the cohomology map induced by an h-map: in degree zero it
corresponds to the map on global sections under the identifications `H^0 ≅ Γ`
(Stacks, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB; Derived Categories, Tags 013P, 013S,
05TG). -/
theorem moduleCohomologyFMap_basic_degree_zero {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) :
    ∃ eG : (Y.toRingedSpace.moduleCohomology 0).obj G ≅
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj G,
      ∃ eF : (X.toRingedSpace.moduleCohomology 0).obj F ≅
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F,
        (forget₂ _ AddCommGrpCat).map eG.hom ≫
            (forget₂ _ AddCommGrpCat).map
              ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) =
          moduleCohomologyFMap h φ 0 ≫
            (forget₂ _ AddCommGrpCat).map eF.hom := by
  let S := RingedSpace.globalSectionsFunctor Y.toRingedSpace
  let T := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : EnoughInjectives Y.Modules := inferInstance
  have : EnoughInjectives X.Modules := inferInstance
  have : PreservesFiniteLimits S :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
  have : PreservesFiniteLimits T :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let eG := S.rightDerivedZeroIsoSelf.app G
  let eF := T.rightDerivedZeroIsoSelf.app F
  refine ⟨eG, eF, ?_⟩
  let a := (forget₂ _ AddCommGrpCat).mapIso eG
  let b := (forget₂ _ AddCommGrpCat).mapIso eF
  have ha : a.inv ≫ moduleCohomologyFMap h φ 0 =
      (forget₂ _ AddCommGrpCat).map (S.map φ) ≫ b.inv :=
    ModuleCohomologyFMapData.map_zero_augmentation
      (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ))
  change a.hom ≫ (forget₂ _ AddCommGrpCat).map (S.map φ) =
    moduleCohomologyFMap h φ 0 ≫ b.hom
  apply (cancel_epi a.inv).mp
  rw [Iso.inv_hom_id_assoc, ← Category.assoc, ha, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
