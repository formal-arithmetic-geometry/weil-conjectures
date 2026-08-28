/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Complements on schemes

* `AlgebraicGeometry.Scheme.isUnit_of_le_basicOpen`: if `U ≤ X.basicOpen f` for a section
  `f : Γ(X, U)`, then `f` is a unit. This is the converse of `Scheme.basicOpen_of_isUnit`.
* `AlgebraicGeometry.Scheme.Hom.range_appLE_subset_of_comp_eq`: sections in the image of
  `appLE` of a composition are in the image of `appLE` of its first factor.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A section of a scheme that is invertible at every point of its domain is a unit.
This is the converse of `Scheme.basicOpen_of_isUnit`. -/
theorem isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {f : Γ(X, U)}
    (h : U ≤ X.basicOpen f) : IsUnit f :=
  X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx ↦ (X.mem_basicOpen f x hx).mp (h hx)

/-- If `f ≫ g = h`, then every section in the image of `h.appLE` also lies in the image of
`f.appLE`. -/
lemma Hom.range_appLE_subset_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hcomp : f ≫ g = h) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) :
    Set.range (h.appLE U W e₃) ⊆ Set.range (f.appLE V W e₂) := by
  subst hcomp
  rintro _ ⟨x, rfl⟩
  exact ⟨g.appLE U V e₁ x, by rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]⟩

end AlgebraicGeometry.Scheme
