/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity

/-! # Linearity property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Linearity property of the cohomology map induced by an h-map: it is the underlying additive
map of a linear map over the restriction of scalars along `h.appTop`
(Stacks, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB; Derived Categories, Tags 013P, 013S,
05TG). -/
theorem moduleCohomologyFMap_basic_linearity {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    ∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = moduleCohomologyFMap h φ p := by
  let D := Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)
  obtain ⟨L, hL⟩ := moduleCohomologyFMapData_map_linear D p
  exact ⟨L, hL.trans rfl⟩

end AlgebraicGeometry.Scheme.Modules
