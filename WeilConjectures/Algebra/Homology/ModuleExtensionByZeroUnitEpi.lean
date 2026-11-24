/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Adjunction.Triple
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-!
# The extension-by-zero unit is epic

The unit of the extension-by-zero/restriction adjunction on module sheaves is an epimorphism.

## References

* Stacks Project, Sheaves, Tag 00A7 (4)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The extension-by-zero/restriction unit is epic. -/
theorem moduleExtensionByZero_unit_epi (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    Epi ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G) := by
  let R := moduleRings X
  let a := Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2
  let b := SheafOfModules.overPushforwardOverAdj (R := R) W
  have : (Over.forget W).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar W).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar W).unit.app V.unop).op)
    infer_instance
  let t : Adjunction.Triple _ _ _ := ⟨a, b⟩
  have : IsIso a.unit := t.isIso_unit_iff_isIso_counit.mpr inferInstance
  infer_instance
end AlgebraicGeometry
