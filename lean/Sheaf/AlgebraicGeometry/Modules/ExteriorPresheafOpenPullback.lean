/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData

/-!
# Exterior presheaves under open pullback

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-presheaf-open-pullback).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The two sectionwise constructions have the same restriction maps by uniqueness on wedges. -/
private theorem exteriorSheafPresheaf_eq_exteriorPower {X : Scheme.{v}}
    (M : X.Modules) (n : ℕ) :
    exteriorSheafPresheaf M n = _root_.PresheafOfModules.exteriorPower M.val n := by
  have hmap : ∀ {V W : X.Opensᵒᵖ} (f : V ⟶ W),
      exteriorSheafRestriction M n f =
        (_root_.PresheafOfModules.exteriorPower M.val n).map f := by
    intro V W f
    apply ((Classical.choose_spec (exteriorSheafRestriction_existsUnique M n f)).2 _ ?_).symm
    intro a
    exact _root_.PresheafOfModules.exteriorPower_map_ιMulti M.val n f a
  unfold exteriorSheafPresheaf _root_.PresheafOfModules.exteriorPower
  congr 1
  funext V W f
  exact hmap f

/-- Pullback of the sectionwise exterior-power presheaf along an open inclusion is the
sectionwise exterior-power presheaf of the restricted module.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-presheaf-open-pullback).

Proof: The section modules of `exteriorSheafPresheaf` and the upstream
`PresheafOfModules.exteriorPower` agree definitionally. Their restriction maps agree
by uniqueness on pure wedges, so the two presheaves are equal. Rewrite both sides
using this equality, apply the upstream component-data theorem, and assemble the
components with `PresheafOfModules.isoMk`. This works for every degree, including
zero, and for empty opens and the empty scheme. -/
theorem exteriorPresheaf_open_pullback {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
      (exteriorSheafPresheaf M n) ≅ exteriorSheafPresheaf (M.restrict U.ι) n) := by
  rw [exteriorSheafPresheaf_eq_exteriorPower M n,
    exteriorSheafPresheaf_eq_exteriorPower (M.restrict U.ι) n]
  obtain ⟨app, happ⟩ := exteriorPresheaf_open_pullback_data M n U
  refine ⟨PresheafOfModules.isoMk app ?_⟩
  intro V W f
  exact happ f

end AlgebraicGeometry.Scheme.Modules
