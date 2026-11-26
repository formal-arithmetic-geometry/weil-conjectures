/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-!
# Products and triangles of derived-complete module complexes

Derived completeness is preserved by countable products and satisfies two-out-of-three in
distinguished triangles.

## Implementation details

Products of modules are exact (also when ring and module universes differ), so countable
products exist in the derived category. Via the Roos triangle, completeness is equivalent to
invertibility of `1 - s` on each multiplication-by-`f` tower product; this is condition (7) of
[Stacks, Tag 091P], used directly instead of the localization/Hom test. For products the inverse
is assembled coordinatewise; for triangles, two-out-of-three for morphisms of distinguished
triangles ([Stacks, Tag 014A]) applies to the three operators `1 - s`.

The first conjunct of the main theorem asserts existence of the product, followed by
completeness for any choice of product structure. The index `n : ℕ` stands for the positive
index `n + 1`. No finite-generation, boundedness, or product-existence hypothesis is imposed.

## References

* [Stacks, Tag 091S]
* [Stacks, Tag 091P]
* [Stacks, Tag 014A]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

private lemma module_countableAB4Star {A : Type u} [CommRing A] :
    CountableAB4Star (ModuleCat.{v} A) := by
  let F := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  let : F.PreservesEpimorphisms := ⟨fun {X Y} f _ ↦ by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective f).mp inferInstance⟩
  let := Functor.preservesHomology_of_preservesEpis_and_kernels F
  let := Functor.preservesFiniteColimits_of_preservesHomology F
  exact ⟨fun J ↦ HasExactLimitsOfShape.domain_of_functor (Discrete J) F⟩

private lemma complete_iff_isIso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    [HasCountableProducts (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A)) :
    IsDerivedComplete I K ↔ ∀ f ∈ I,
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K)) := by
  constructor
  · intro h f hf
    obtain ⟨L, p, δ, hT⟩ := distinguished_cocone_triangle₁
      (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K))
    exact (Triangle.isZero₁_iff_isIso₂ _ hT).mp (h f hf L ⟨p, δ, hT⟩)
  · intro h f hf _ L ⟨p, δ, hT⟩
    exact (Triangle.isZero₁_iff_isIso₂ _ hT).mpr (h f hf)

private lemma tower_isIso_product {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    [HasCountableProducts (DerivedCategory (ModuleCat.{v} A))]
    (K : ℕ → DerivedCategory (ModuleCat.{v} A)) (f : A)
    (h : ∀ n, IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ K n) (fun _ ↦ f • 𝟙 (K n)))) :
    IsIso (towerTransitionEndomorphism
      (K := fun _ : ℕ ↦ ∏ᶜ K) (fun _ ↦ f • 𝟙 (∏ᶜ K))) := by
  let t (X : DerivedCategory (ModuleCat.{v} A)) :=
    towerTransitionEndomorphism (K := fun _ : ℕ ↦ X) (fun _ ↦ f • 𝟙 X)
  let γ (n : ℕ) : (∏ᶜ fun _ : ℕ ↦ ∏ᶜ K) ⟶ (∏ᶜ fun _ : ℕ ↦ K n) :=
    Limits.Pi.map (fun _ ↦ Pi.π K n)
  have ht (n : ℕ) : t (∏ᶜ K) ≫ γ n = γ n ≫ t (K n) := by
    symm
    apply towerTransitionEndomorphism_natural_backward
    intro j
    simp [Linear.comp_smul, Linear.smul_comp]
  let _ (n : ℕ) : IsIso (t (K n)) := h n
  let q : (∏ᶜ fun _ : ℕ ↦ ∏ᶜ K) ⟶ (∏ᶜ fun _ : ℕ ↦ ∏ᶜ K) :=
    Pi.lift (fun j ↦ Pi.lift (fun n ↦ γ n ≫ inv (t (K n)) ≫ Pi.π _ j))
  have hq (n : ℕ) : q ≫ γ n = γ n ≫ inv (t (K n)) := by
    apply Pi.hom_ext
    intro j
    simp [q, γ, Category.assoc]
  have hext {X : DerivedCategory (ModuleCat.{v} A)}
      (a b : X ⟶ (∏ᶜ fun _ : ℕ ↦ ∏ᶜ K))
      (hab : ∀ n, a ≫ γ n = b ≫ γ n) : a = b := by
    apply Pi.hom_ext
    intro j
    apply Pi.hom_ext
    intro n
    have e := congrArg (fun z ↦ z ≫ Pi.π (fun _ : ℕ ↦ K n) j) (hab n)
    simpa [γ, Category.assoc] using e
  change IsIso (t (∏ᶜ K))
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply hext
    intro n
    rw [Category.id_comp, Category.assoc, hq, ← Category.assoc, ht,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · apply hext
    intro n
    rw [Category.id_comp, Category.assoc, ht, ← Category.assoc, hq,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private lemma tower_triangle_endomorphism {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)]
    [HasCountableProducts (DerivedCategory (ModuleCat.{v} A))]
    (T : Triangle (DerivedCategory (ModuleCat.{v} A))) (f : A) :
    ∃ φ : productTriangle (fun _ : ℕ ↦ T) ⟶ productTriangle (fun _ : ℕ ↦ T),
      φ.hom₁ = towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ T.obj₁) (fun _ ↦ f • 𝟙 T.obj₁) ∧
      φ.hom₂ = towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ T.obj₂) (fun _ ↦ f • 𝟙 T.obj₂) ∧
      φ.hom₃ = towerTransitionEndomorphism
        (K := fun _ : ℕ ↦ T.obj₃) (fun _ ↦ f • 𝟙 T.obj₃) := by
  exact ⟨𝟙 _ - productTriangle.lift (fun _ : ℕ ↦ T)
    (fun n ↦ productTriangle.π (fun _ : ℕ ↦ T) (n + 1) ≫ (f • 𝟙 T)), rfl, rfl, rfl⟩

/-- Derived completeness for any ideal is preserved by countable products and satisfies
two-out-of-three in distinguished triangles of the unbounded module derived category. -/
theorem isDerivedComplete_products_and_triangles {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A) :
    (∀ (K : ℕ → DerivedCategory (ModuleCat.{v} A)),
      (∀ n : ℕ, IsDerivedComplete I (K n)) →
        HasProduct K ∧ ∀ [HasProduct K], IsDerivedComplete I (∏ᶜ K)) ∧
    (∀ (T : Triangle (DerivedCategory (ModuleCat.{v} A))),
      T ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) →
        (IsDerivedComplete I T.obj₁ → IsDerivedComplete I T.obj₂ →
          IsDerivedComplete I T.obj₃) ∧
        (IsDerivedComplete I T.obj₁ → IsDerivedComplete I T.obj₃ →
          IsDerivedComplete I T.obj₂) ∧
        (IsDerivedComplete I T.obj₂ → IsDerivedComplete I T.obj₃ →
          IsDerivedComplete I T.obj₁)) := by
  classical
  let := module_countableAB4Star (A := A)
  let _ : HasCountableProducts (DerivedCategory (ModuleCat.{v} A)) :=
    derivedCategory_hasCountableProducts (ModuleCat.{v} A)
  constructor
  · intro K hK
    refine ⟨inferInstance, ?_⟩
    intro _
    apply (complete_iff_isIso I _).mpr
    intro f hf
    exact tower_isIso_product K f (fun n ↦ (complete_iff_isIso I (K n)).mp (hK n) f hf)
  · intro T hT
    have hpT := productTriangle_distinguished (fun _ : ℕ ↦ T) (fun _ ↦ hT)
    refine ⟨?_, ?_, ?_⟩
    · intro h₁ h₂
      apply (complete_iff_isIso I _).mpr
      intro f hf
      obtain ⟨φ, e₁, e₂, e₃⟩ := tower_triangle_endomorphism T f
      rw [← e₃]
      exact isIso₃_of_isIso₁₂ φ hpT hpT
        (e₁.symm ▸ (complete_iff_isIso I _).mp h₁ f hf)
        (e₂.symm ▸ (complete_iff_isIso I _).mp h₂ f hf)
    · intro h₁ h₃
      apply (complete_iff_isIso I _).mpr
      intro f hf
      obtain ⟨φ, e₁, e₂, e₃⟩ := tower_triangle_endomorphism T f
      rw [← e₂]
      exact isIso₂_of_isIso₁₃ φ hpT hpT
        (e₁.symm ▸ (complete_iff_isIso I _).mp h₁ f hf)
        (e₃.symm ▸ (complete_iff_isIso I _).mp h₃ f hf)
    · intro h₂ h₃
      apply (complete_iff_isIso I _).mpr
      intro f hf
      obtain ⟨φ, e₁, e₂, e₃⟩ := tower_triangle_endomorphism T f
      rw [← e₁]
      exact isIso₁_of_isIso₂₃ φ hpT hpT
        (e₂.symm ▸ (complete_iff_isIso I _).mp h₂ f hf)
        (e₃.symm ▸ (complete_iff_isIso I _).mp h₃ f hf)

end DerivedCategory
