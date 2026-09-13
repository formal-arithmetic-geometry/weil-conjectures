/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Units among the sections over a basic open, `Scheme.Hom.appLE`, and the preimage of `⊤`

We record that the restriction of a section `s` of the structure sheaf to any open contained
in `X.basicOpen s` is a unit, that `Scheme.Hom.appLE` only depends on the morphism up to
equality, that `Scheme.Hom.appLE` between the top opens is `Scheme.Hom.appTop`, and that any
presheaf on `X` sends the inclusion `⊤ ≤ a ⁻¹ᵁ ⊤` to the identity, the preimage of `⊤` under a
morphism of schemes being `⊤`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Any presheaf on `X` sends the inclusion `⊤ ≤ a ⁻¹ᵁ ⊤` to the identity: the preimage of `⊤`
under a morphism of schemes is `⊤`, see `AlgebraicGeometry.Scheme.Hom.preimage_top`, so this
inclusion is the identity morphism of `⊤` in `X.Opens`. -/
lemma Scheme.presheaf_map_homOfLE_preimage_top_eq_id {C : Type*} [Category C] {Y : Scheme.{u}}
    (F : X.Opensᵒᵖ ⥤ C) (a : X ⟶ Y) :
    F.map (homOfLE (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)).op = 𝟙 (F.obj (op ⊤)) :=
  (congrArg (fun i : (op (a ⁻¹ᵁ ⊤) : X.Opensᵒᵖ) ⟶ op ⊤ ↦ F.map i)
    (Subsingleton.elim _ (𝟙 (op (⊤ : X.Opens))))).trans (F.map_id _)

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
  subst hcd
  rfl

/-- `Scheme.Hom.appLE` from the top open to the top open is `Scheme.Hom.appTop`. -/
lemma appLE_eq_appTop (a : X ⟶ Y) (e : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤) : a.appLE ⊤ ⊤ e = a.appTop := by
  have h : (homOfLE e).op = 𝟙 (op (a ⁻¹ᵁ ⊤) : X.Opensᵒᵖ) := Subsingleton.elim _ _
  rw [Hom.appLE, h, X.presheaf.map_id, Category.comp_id]

end Scheme.Hom

end AlgebraicGeometry
