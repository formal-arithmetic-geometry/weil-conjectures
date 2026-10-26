/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Left adjoints preserve natural families of endomorphisms

Let `L ⊣ R` be an adjunction between categories `C` and `D`, each equipped with a family of
endomorphisms `s X : X ⟶ X` commuting with all morphisms (for instance the multiplication by a
scalar `r` in an `R`-linear category, `R` commutative). If the right adjoint sends `s` to `s`,
then so does the left adjoint (`CategoryTheory.Adjunction.map_eq_of_rightAdjoint_map_eq`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- Let `sC`, `sD` be families of endomorphisms commuting with all morphisms of `C`, resp.
`D`. If the right adjoint `R` sends `sD` to `sC`, then the left adjoint `L` sends `sC` to
`sD`. -/
lemma map_eq_of_rightAdjoint_map_eq (adj : L ⊣ R) (sC : ∀ X : C, X ⟶ X) (sD : ∀ Y : D, Y ⟶ Y)
    (hC : ∀ {X X' : C} (f : X ⟶ X'), f ≫ sC X' = sC X ≫ f)
    (hR : ∀ Y : D, R.map (sD Y) = sC (R.obj Y)) (X : C) :
    L.map (sC X) = sD (L.obj X) := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, hR]
  exact (adj.unit.naturality (sC X)).symm.trans (hC (adj.unit.app X)).symm

end CategoryTheory.Adjunction
