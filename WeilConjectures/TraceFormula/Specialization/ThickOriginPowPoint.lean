/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowFibre

/-!

# Rational points of the special fibres of the power model

A section of a scheme `X ⟶ Spec K` over a field is determined by its point
(`AlgebraicGeometry.Scheme.ext_of_comp_eq_id_of_apply_eq`). For a `k`-scheme `Y` with a
rational point `y`, the special fibre of the constant family `Y × S` has the `k'`-point
`constantFamilySpecialPoint` lying over `y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- A morphism `Spec K ⟶ X` which is a section of `h : X ⟶ Spec K` is determined by its residue
field map: the residue field map is the inverse of `K ⟶ κ(x)`. -/
lemma residueField_hom_eq_of_section {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) {x : X} (φ₁ φ₂ : X.residueField x ⟶ .of K)
    (h₁ : Spec.map φ₁ ≫ X.fromSpecResidueField x ≫ h = 𝟙 _)
    (h₂ : Spec.map φ₂ ≫ X.fromSpecResidueField x ≫ h = 𝟙 _) : φ₁ = φ₂ := by
  set ψ := Spec.preimage (X.fromSpecResidueField x ≫ h)
  have hψ : Spec.map ψ = X.fromSpecResidueField x ≫ h := Spec.map_preimage _
  have e₁ : ψ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hψ, h₁, Spec.map_id])
  have e₂ : ψ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, hψ, h₂, Spec.map_id])
  ext z
  have hz : ψ (φ₁ z) = z := by
    apply φ₁.hom.injective
    exact congr($(e₁) (φ₁ z))
  rw [← hz]
  exact (congr($(e₁) (φ₁ z))).trans (congr($(e₂) (φ₁ z))).symm

/-- Two sections `Spec K ⟶ X` of `h : X ⟶ Spec K` with the same point are equal. -/
lemma ext_of_comp_eq_id_of_apply_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of K)) {f g : Spec (.of K) ⟶ X} (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g := by
  obtain ⟨⟨x, φ₁⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective f
  obtain ⟨⟨y, φ₂⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective g
  simp only [SpecToEquivOfField_symm_apply, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] at H
  subst H
  simp only [SpecToEquivOfField_symm_apply, Category.assoc] at hf hg ⊢
  rw [residueField_hom_eq_of_section h φ₁ φ₂ hf hg]

end Scheme

end AlgebraicGeometry
