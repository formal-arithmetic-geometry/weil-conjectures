/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Preimages of opens under a morphism of schemes

Mathlib records that taking preimages of opens commutes with arbitrary suprema
(`AlgebraicGeometry.Scheme.Hom.preimage_iSup`). Infima of opens are only intersections when
indexed by a finite type, and in that case preimages commute with them as well:

- `AlgebraicGeometry.Scheme.Hom.preimage_iInf`.

We also record that a global section whose non-vanishing locus is everything is a unit:

- `AlgebraicGeometry.Scheme.isUnit_of_basicOpen_eq_top`.

# Complements on schemes

* `AlgebraicGeometry.Scheme.isUnit_of_le_basicOpen`: if `U ≤ X.basicOpen f` for a section
  `f : Γ(X, U)`, then `f` is a unit. This is the converse of `Scheme.basicOpen_of_isUnit`.
* `AlgebraicGeometry.Scheme.Hom.range_appLE_subset_of_comp_eq`: sections in the image of
  `appLE` of a composition are in the image of `appLE` of its first factor.
* `AlgebraicGeometry.Scheme.IsSpecOfField`: the scheme is isomorphic to the spectrum of a
  field.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Taking preimages of opens commutes with finite infima. -/
lemma preimage_iInf {ι : Type*} [Finite ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ ⨅ i, U i = ⨅ i, f ⁻¹ᵁ U i :=
  Opens.ext <| by
    simp only [coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- A global section that vanishes nowhere is a unit. -/
lemma isUnit_of_basicOpen_eq_top {X : Scheme.{u}} (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ ↦ ?_
  exact (X.mem_basicOpen_top f x).mp (h.ge trivial)

end AlgebraicGeometry.Scheme

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
/-- If `f ≫ g = h`, then every section in the image of `h.appLE` also lies in the image of
`f.appLE`. -/
lemma Hom.range_appLE_subset_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hcomp : f ≫ g = h) {U : Z.Opens} {V : Y.Opens} {W : X.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) :
    Set.range (h.appLE U W e₃) ⊆ Set.range (f.appLE V W e₂) := by
  subst hcomp
  rintro _ ⟨x, rfl⟩
  exact ⟨g.appLE U V e₁ x, by rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]⟩

/-- A scheme `S` *is the spectrum of a field* if it is isomorphic to `Spec k` for some field
`k`. -/
def IsSpecOfField (S : Scheme.{u}) : Prop :=
  ∃ (k : Type u) (_ : Field k), Nonempty (S ≅ Spec (.of k))

end AlgebraicGeometry.Scheme
