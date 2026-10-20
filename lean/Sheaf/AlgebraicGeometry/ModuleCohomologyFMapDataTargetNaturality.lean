/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Target coefficient naturality for arbitrary resolution data

Source: Stacks Project, Tags 01F8, 01F9 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-target-naturality).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Changing the target module commutes with the resolution formula, even when
its two computations use different resolutions.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01F8 and Remark 01FB;
Derived Categories, Lemmas 013P, 013S and 05TG
(blueprint: lem-weil-pbc-module-cohomology-fmap-data-target-naturality).

Proof: apply independence of resolution data to D and the datum used in the
canonical map, and similarly to E. Rewrite both maps using these equalities.
Canonical target naturality, obtained from composition and the identity-scheme
case, then gives the result. No invertibility of b is required. -/
theorem ModuleCohomologyFMapData.map_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (b : F ⟶ F')
    (D : ModuleCohomologyFMapData h G F φ)
    (E : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) (p : ℕ) :
    D.map p ≫ (forget₂ _ AddCommGrpCat.{u}).map
        ((X.toRingedSpace.moduleCohomology p).map b) = E.map p := by
  have hD : D.map p = moduleCohomologyFMap h φ p :=
    moduleCohomologyFMap_independent h φ D
      (Classical.choice (moduleCohomologyFMapData_nonempty h G F φ)) p
  have hE : E.map p = moduleCohomologyFMap h (φ ≫ (pushforward h).map b) p :=
    moduleCohomologyFMap_independent h (φ ≫ (pushforward h).map b) E
      (Classical.choice (moduleCohomologyFMapData_nonempty h G F'
        (φ ≫ (pushforward h).map b))) p
  rw [hD, hE]
  exact moduleCohomologyFMap_target_naturality h b φ p

end AlgebraicGeometry.Scheme.Modules
