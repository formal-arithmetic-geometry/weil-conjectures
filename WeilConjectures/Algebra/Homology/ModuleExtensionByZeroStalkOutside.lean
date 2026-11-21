/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of the extension by zero at points outside the open

The stalk of the sheafified extension by zero at a point outside `W` is zero.

## References

* Stacks Project, Sheaves, Tag 00A7 (3), via Tags 00A5 and 007Z
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
universe u
noncomputable section
namespace AlgebraicGeometry
/-- For a ringed space X, open W, module sheaf G on the localized opens of W, and x outside W, the
stalk at x of the module sheafification of the direct-sum extension-by-zero presheaf of G is the
zero module over O_X,x. -/
theorem moduleExtensionByZero_stalk_outside (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (G : SheafOfModules.{u} ((moduleRings X).over W)) (x : X),
      x ∉ W → IsZero ((RingedSpace.moduleStalkFunctor X x).obj
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj G)))
 := by
  intro W G x hx
  let P := (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W).obj G
  have hp : IsZero (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) P.presheaf x) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    suffices hh : ∀ s : TopCat.Presheaf.stalk (C := Ab.{u})
        (X := X.carrier) P.presheaf x, s = 0 from
      ⟨fun a b => (hh a).trans (hh b).symm⟩
    intro s
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X.carrier) P.presheaf s
    have : IsEmpty (V ⟶ W) := ⟨fun f => hx (f.le hxV)⟩
    have hs : s = 0 := by
      change SheafOfModules.extensionByZeroPresheafSection (moduleRings X) W G (op V) at s
      exact (SheafOfModules.extensionByZeroPresheafSection_isEmpty
        (moduleRings X) W G (op V)).elim s 0
    rw [hs]
    exact map_zero _
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab.{u} P.presheaf
  have hq := hp.of_iso (asIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    (toSheafify (Opens.grothendieckTopology X) P.presheaf))).symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hq

end AlgebraicGeometry
