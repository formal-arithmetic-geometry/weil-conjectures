/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData

/-!
# Exterior sheaves commute with open restriction

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-restrict-iso).
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

/-- Sheafifying the equal exterior presheaves identifies the two exterior sheaves. -/
private theorem exteriorSheaf_eq_exteriorPower {X : Scheme.{v}}
    (M : X.Modules) (n : ℕ) : exteriorSheaf M n = exteriorPower M n := by
  unfold exteriorSheaf exteriorPower sheafificationObj
  rw [exteriorSheafPresheaf_eq_exteriorPower M n]

/-- Formation of the exterior sheaf commutes with restriction to an open subscheme.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-restrict-iso).

Proof: For an open V of U, the sections of the restricted module are the sections of M
on the same open viewed in X; likewise the scalar rings agree. These identifications
induce equivalences of their nth exterior powers. On a pure wedge, restriction in both
presheaves is the wedge of the restrictions of its factors, by the characterizing
property of exteriorSheafRestriction_existsUnique. Pure wedges span, so these
identifications are natural and identify the exterior presheaf on U with the restriction
of the exterior presheaf on X. Sheafification commutes with open restriction: the
sheafified sections are represented locally by presheaf sections, with equality checked
after a covering refinement, and the covers of an open in U are exactly its covers in X.
Sheafify the presheaf identification and compose with this restriction comparison.
This gives the displayed isomorphism, with no freeness hypothesis. The construction
also applies to degree zero and to the empty open subscheme. -/
theorem exteriorSheaf_restrict_iso {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((exteriorSheaf M n).restrict U.ι ≅ exteriorSheaf (M.restrict U.ι) n) := by
  have h := exteriorSheaf_restrict_hom_data M n U
  rw [← exteriorSheaf_eq_exteriorPower M n,
    ← exteriorSheaf_eq_exteriorPower (M.restrict U.ι) n] at h
  obtain ⟨e, f, hef, hfe⟩ := h
  exact ⟨{ hom := e, inv := f, hom_inv_id := hef, inv_hom_id := hfe }⟩

end AlgebraicGeometry.Scheme.Modules
