/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-! # Compatibility of the two sectionwise exterior-power presheaves -/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The original sectionwise exterior presheaf equals the upstream construction.
Source: the universal property of exterior powers, as implemented in
`exteriorSheafRestriction_existsUnique` and `PresheafOfModules.exteriorPower_map_ιMulti`.
(blueprint: lem-sc-exterior-sheaf-presheaf-upstream-comparison).

Proof: the objects agree definitionally. On each restriction, the upstream map takes
pure wedges to wedges of restricted sections, so uniqueness in the original universal
property identifies the two restriction maps. Structure extensionality then identifies
the presheaves. The argument includes degree zero and zero rings. -/
theorem exteriorSheafPresheaf_eq_exteriorPower {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n =
      _root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val n := by
  have hm : ∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V),
      exteriorSheafRestriction M n f =
        (_root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).map f := by
    intro U V f
    exact ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2 _
      (fun a ↦ _root_.PresheafOfModules.exteriorPower_map_ιMulti M.val n f a)).symm
  unfold exteriorSheafPresheaf _root_.PresheafOfModules.exteriorPower
  congr 1
  funext U V f
  exact hm f

end AlgebraicGeometry.Scheme.Modules
