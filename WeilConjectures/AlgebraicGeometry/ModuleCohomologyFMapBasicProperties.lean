/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.BasicPropertiesLinearity
import WeilConjectures.AlgebraicGeometry.BasicPropertiesDegreeZero
import WeilConjectures.AlgebraicGeometry.BasicPropertiesIdentity
import WeilConjectures.AlgebraicGeometry.BasicPropertiesRestriction

/-! # Basic properties of maps on module cohomology

## References

* [Stacks, Cohomology of Sheaves, Tags 01F7, 01F8, 01FA, 01FB]
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Linearity, degree zero, identity, and restriction properties of the map induced by an
`h`-map. The degree-zero clause is expressed using the canonical derived-functor
identifications with global sections (Stacks, Tag 01F7). -/
theorem moduleCohomologyFMap_basic_properties {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = moduleCohomologyFMap h φ p) ∧
    (∃ eG : (Y.toRingedSpace.moduleCohomology 0).obj G ≅
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj G,
      ∃ eF : (X.toRingedSpace.moduleCohomology 0).obj F ≅
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F,
        (forget₂ _ AddCommGrpCat).map eG.hom ≫
            (forget₂ _ AddCommGrpCat).map
              ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) =
          moduleCohomologyFMap h φ 0 ≫
            (forget₂ _ AddCommGrpCat).map eF.hom) ∧
    (∀ (Z : Scheme.{u}) (GZ FZ : SheafOfModules.{u} Z.ringCatSheaf)
      (ψ : GZ ⟶ FZ),
      moduleCohomologyFMap (𝟙 Z) ψ p =
        (forget₂ _ AddCommGrpCat).map
          ((Z.toRingedSpace.moduleCohomology p).map ψ)) ∧
    (∀ (U : Y.Opens),
      ∃ κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G,
        moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p ≫
            (forget₂ _ AddCommGrpCat).map
              (((U : Scheme).toRingedSpace.moduleCohomology p).map κ.hom) =
          moduleCohomologyFMap U.ι
            ((Classical.choose (exists_tensorPullbackAdjunction U.ι)).unit.app G) p)
 := by
  refine ⟨moduleCohomologyFMap_basic_linearity h φ p, ?_, ?_, ?_⟩
  · exact moduleCohomologyFMap_basic_degree_zero h φ
  · intro Z GZ FZ ψ
    exact moduleCohomologyFMap_basic_identity GZ FZ ψ p
  · exact moduleCohomologyFMap_basic_restriction G p

end AlgebraicGeometry.Scheme.Modules
