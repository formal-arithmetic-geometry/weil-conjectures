/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData

/-!
# Exterior sheaves commute with open restriction

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-restrict-iso).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

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
  obtain ⟨e, f, hef, hfe⟩ := exteriorSheaf_restrict_hom_data M n U
  exact ⟨{ hom := e, inv := f, hom_inv_id := hef, inv_hom_id := hfe }⟩

end AlgebraicGeometry.Scheme.Modules
