/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange

/-!
# The Thom isomorphism for the compactly supported direct image of a vector bundle

Let `π : V ⟶ S` be a vector bundle with zero section `z` (`AlgebraicGeometry.VectorBundle`).

* **The trace is an isomorphism.** The counit `Rπ_! Rπ^! Λ_S ⟶ Λ_S` is an isomorphism
  (`AlgebraicGeometry.VectorBundle.isIso_counit_constantComplex`). It has a section: as
  `z ≫ π = 𝟙`, the counit of the composite adjunction `Rπ_! Rz_! ⊣ Rz^! Rπ^!` is invertible, and
  it factors through it. On every chart `π⁻¹ U ≅ 𝔸^d_U` the source is isomorphic to `Λ_U`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`), and an
  endomorphism of the unit with a one-sided inverse is invertible, endomorphisms of the unit of a
  monoidal category commuting with each other.
* **The rank-one Thom isomorphism** (`thm-pur-rank-one-thom`). For a line bundle, with the Thom
  class `thom(E) : z_* Λ_S ⟶ Λ_V(1)[2]` (the class of the zero divisor), `τ_E = Rπ_! thom(E)` is
  an isomorphism (`AlgebraicGeometry.VectorBundle.isIso_rightDerivedLowerShriek_map_thom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Endomorphisms of the unit of a monoidal category commute (Eckmann–Hilton). -/
lemma endUnit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have h := whisker_exchange f g
  rw [← cancel_epi (λ_ (𝟙_ C)).inv, ← cancel_mono (λ_ (𝟙_ C)).hom]
  have hf : f ▷ 𝟙_ C = (λ_ (𝟙_ C)).hom ≫ f ≫ (λ_ (𝟙_ C)).inv := by
    rw [unitors_equal, rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have hg : 𝟙_ C ◁ g = (λ_ (𝟙_ C)).hom ≫ g ≫ (λ_ (𝟙_ C)).inv := by
    rw [leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hf, hg] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  simpa using congrArg (fun φ ↦ (λ_ (𝟙_ C)).inv ≫ φ ≫ (λ_ (𝟙_ C)).hom) h.symm

/-- A morphism `r : T ⟶ N` with a right inverse `s`, between objects isomorphic to the unit, is an
isomorphism. -/
lemma isIso_of_comp_eq_id_of_iso_unit {N T : C} (e : N ≅ 𝟙_ C) (φ : T ≅ N) (s : N ⟶ T)
    (r : T ⟶ N) (h : s ≫ r = 𝟙 N) : IsIso r := by
  have hxy := endUnit_comm (e.inv ≫ s ≫ φ.hom ≫ e.hom) (e.inv ≫ φ.inv ≫ r ≫ e.hom)
  have h₁ : (e.inv ≫ s ≫ φ.hom ≫ e.hom) ≫ (e.inv ≫ φ.inv ≫ r ≫ e.hom) = 𝟙 _ := by
    simp [h]
  rw [h₁] at hxy
  have h₂ : r ≫ s = 𝟙 T := by
    have := congrArg (fun ψ ↦ φ.hom ≫ e.hom ≫ ψ ≫ e.inv ≫ φ.inv) hxy
    simpa using this.symm
  exact ⟨s, h₂, h⟩

end CategoryTheory.MonoidalCategory

end
