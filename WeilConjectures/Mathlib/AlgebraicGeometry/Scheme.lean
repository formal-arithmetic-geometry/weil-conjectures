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
* `AlgebraicGeometry.Scheme.Hom.appLE_top_top`: `appLE` between the top opens is `appTop`.
* `AlgebraicGeometry.Scheme.specMap_appTop_ΓSpecIso_inv` and
  `AlgebraicGeometry.Scheme.ΓSpecIso_inv_mul`: compatibility of the global-sections
  isomorphism of an affine scheme with `Spec` of a ring map and with multiplication.
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

/-- The `appLE` of a morphism between the top opens is its `appTop`. -/
lemma Hom.appLE_top_top {T T' : Scheme.{u}} (q : T ⟶ T')
    (h : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤) : q.appLE ⊤ ⊤ h = q.appTop := by
  simp [Scheme.Hom.appLE]

/-- `Spec` of a ring map acts on global sections by the ring map. -/
lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- Multiplicativity of the inverse of `ΓSpecIso`. -/
lemma ΓSpecIso_inv_mul {R : CommRingCat.{u}} (r s : R) :
    (Scheme.ΓSpecIso R).inv r * (Scheme.ΓSpecIso R).inv s = (Scheme.ΓSpecIso R).inv (r * s) :=
  (map_mul _ _ _).symm

end AlgebraicGeometry.Scheme
