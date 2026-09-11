/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Units among the sections over a basic open, and two lemmas on `Scheme.Hom.appLE`

We record that the restriction of a section `s` of the structure sheaf to any open contained
in `X.basicOpen s` is a unit, that `Scheme.Hom.appLE` only depends on the morphism up to
equality, and that `Scheme.Hom.appLE` between the top opens is `Scheme.Hom.appTop`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The restriction of a section `s` to any open contained in `X.basicOpen s` is a unit. -/
lemma Scheme.isUnit_res_of_le_basicOpen {s : Γ(X, ⊤)} {U : X.Opens} (hU : U ≤ X.basicOpen s) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) := by
  have h : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
      X.presheaf.map (homOfLE (X.basicOpen_le s)).op ≫ X.presheaf.map (homOfLE hU).op := by
    rw [← Functor.map_comp, ← op_comp]
    rfl
  rw [h, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (X.toRingedSpace.isUnit_res_basicOpen s).map (X.presheaf.map (homOfLE hU).op).hom

/-- The restriction of a section `f` to `X.basicOpen f` is a unit. -/
lemma Scheme.isUnit_algebraMap_basicOpen {U : X.Opens} (f : Γ(X, U)) :
    IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) f) :=
  X.toRingedSpace.isUnit_res_basicOpen f

namespace Scheme.Hom

variable {Y : Scheme.{u}}

/-- `Scheme.Hom.appLE` only depends on the morphism up to equality. -/
lemma appLE_congr_hom {c d : X ⟶ Y} (hcd : c = d) (U : Y.Opens) (V : X.Opens)
    (ec : V ≤ c ⁻¹ᵁ U) (ed : V ≤ d ⁻¹ᵁ U) : c.appLE U V ec = d.appLE U V ed := by
  subst hcd; rfl

/-- `Scheme.Hom.appLE` from the top open to the top open is `Scheme.Hom.appTop`. -/
lemma appLE_top_top (a : X ⟶ Y) (e : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤) : a.appLE ⊤ ⊤ e = a.appTop := by
  have h : (homOfLE e).op = 𝟙 (op (a ⁻¹ᵁ ⊤) : X.Opensᵒᵖ) := Subsingleton.elim _ _
  rw [Hom.appLE, h, X.presheaf.map_id, Category.comp_id]

end Scheme.Hom

end AlgebraicGeometry
