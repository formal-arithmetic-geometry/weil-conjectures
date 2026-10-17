/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The tensor map of a right adjoint with a linear counit

Let `adj : L ⊣ R` be an adjunction between monoidal categories with an invertible projection map
`π M N : L M ⊗ N ⟶ L (M ⊗ F N)` (a compactly supported direct image `f_!`, its right adjoint
`f^!` and the pullback `F = f^*`), and let `τ` be its tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`). Suppose that `L` has a second right adjoint
of the special form `N ↦ ω ⊗ F N`, whose counit is *linear*: it is

`L (ω ⊗ F N) ≅ L ω ⊗ N ⟶ 𝟙 ⊗ N ≅ N`,

the inverse of the projection map followed by a fixed morphism `t : L ω ⟶ 𝟙` tensored with `N`
(for the projective line, `t` is the trace). Then the tensor map `τ 𝟙 N : R 𝟙 ⊗ F N ⟶ R (𝟙 ⊗ N)`
is an isomorphism for every `N`, and the transpose `ω ⟶ R 𝟙` of `t` is an isomorphism.

This is the formal step in the proof of smooth duality (blueprint `thm-asd-smooth-tensor`): an
abstract identification `f^! ≅ ω ⊗ f^*` does not make the canonical map `f^! 𝟙 ⊗ f^* N ⟶ f^! N`
an isomorphism, but an identification whose counit is linear does.

## Main statements

- `CategoryTheory.Adjunction.isIso_projectionTensorMap_of_bijective`
- `CategoryTheory.Adjunction.isIso_homEquiv_linearCounit`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The linear counit `L (ω ⊗ F N) ≅ L ω ⊗ N ⟶ 𝟙 ⊗ N ≅ N` attached to `t : L ω ⟶ 𝟙`. -/
noncomputable abbrev linearCounit (ω : C) (t : L.obj ω ⟶ 𝟙_ D) (N : D) :
    L.obj (ω ⊗ F.obj N) ⟶ N :=
  inv (π ω N) ≫ t ▷ N ≫ (λ_ N).hom

/-- The transpose of `t : L ω ⟶ 𝟙`, followed by the tensor map, is the transpose of the linear
counit. -/
lemma homEquiv_whiskerRight_comp_projectionTensorMap
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (ω : C) (t : L.obj ω ⟶ 𝟙_ D) (N : D) :
    adj.homEquiv _ _ t ▷ F.obj N ≫ adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom =
      adj.homEquiv _ _ (linearCounit π ω t N) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm, homEquiv_symm_projectionTensorMap]
  have h := hπ (adj.homEquiv _ _ t) N
  rw [← cancel_epi (inv (π ω N)), ← cancel_mono (inv (π _ N))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [reassoc_of% h.symm, ← comp_whiskerRight_assoc, ← homEquiv_counit, Equiv.symm_apply_apply]

/-- If the functor `N ↦ ω ⊗ F N` is right adjoint to `L` with the linear counit attached to
`t : L ω ⟶ 𝟙`, that is, if every `L P ⟶ N` factors uniquely through the linear counit, then the
transpose `ω ⊗ F N ⟶ R N` of the linear counit is an isomorphism. -/
theorem isIso_homEquiv_linearCounit (ω : C) (t : L.obj ω ⟶ 𝟙_ D)
    (h : ∀ (P : C) (N : D), Function.Bijective fun φ : P ⟶ ω ⊗ F.obj N ↦
      L.map φ ≫ linearCounit π ω t N) (N : D) :
    IsIso (adj.homEquiv _ _ (linearCounit π ω t N)) := by
  refine isIso_of_yoneda_map_bijective _ fun P ↦ ?_
  have : (fun x : P ⟶ ω ⊗ F.obj N ↦ x ≫ adj.homEquiv _ _ (linearCounit π ω t N)) =
      adj.homEquiv _ _ ∘ fun φ ↦ L.map φ ≫ linearCounit π ω t N := by
    ext φ
    simp only [Function.comp_apply, ← adj.homEquiv_naturality_left]
  rw [this]
  exact (adj.homEquiv _ _).bijective.comp (h P N)

variable {π} in
/-- **The tensor map of a right adjoint with a linear counit is an isomorphism.** If the
projection map is natural in its first variable, `F 𝟙` is invertible, and the functor
`N ↦ ω ⊗ F N` is right adjoint to `L` with the linear counit attached to some `t : L ω ⟶ 𝟙`,
then the tensor map `τ 𝟙 N : R 𝟙 ⊗ F N ⟶ R (𝟙 ⊗ N)` is an isomorphism for every `N`. -/
theorem isIso_projectionTensorMap_of_bijective
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (hF : IsInvertible (F.obj (𝟙_ D))) (ω : C) (t : L.obj ω ⟶ 𝟙_ D)
    (h : ∀ (P : C) (N : D), Function.Bijective fun φ : P ⟶ ω ⊗ F.obj N ↦
      L.map φ ≫ linearCounit π ω t N) (N : D) :
    IsIso (adj.projectionTensorMap π (𝟙_ D) N) ∧ IsIso (adj.homEquiv _ _ t) := by
  have key (N : D) := homEquiv_whiskerRight_comp_projectionTensorMap adj π hπ ω t N
  have hκ (N : D) := isIso_homEquiv_linearCounit adj π ω t h N
  have hτ₁ : IsIso (adj.projectionTensorMap π (𝟙_ D) (𝟙_ D)) :=
    isIso_projectionTensorMap_of_isInvertible adj π hπ isInvertible_unit hF _
  have hψ : IsIso (adj.homEquiv _ _ t) := by
    have h₁ : IsIso (adj.homEquiv _ _ t ▷ F.obj (𝟙_ D)) := by
      have := hκ (𝟙_ D)
      rw [← key] at this
      have : IsIso (adj.homEquiv _ _ t ▷ F.obj (𝟙_ D) ≫
          adj.projectionTensorMap π (𝟙_ D) (𝟙_ D)) :=
        IsIso.of_isIso_comp_right _ (R.map (λ_ (𝟙_ D)).hom)
      exact IsIso.of_isIso_comp_right _ (adj.projectionTensorMap π (𝟙_ D) (𝟙_ D))
    obtain ⟨Y, ⟨e₁⟩, ⟨e₂⟩⟩ := hF
    exact isIso_of_reflects_iso (adj.homEquiv _ _ t)
      (tensorRightEquivalenceOfTensorIso e₁ e₂).functor
  refine ⟨?_, hψ⟩
  have := hκ N
  rw [← key] at this
  have : IsIso (adj.homEquiv _ _ t ▷ F.obj N ≫ adj.projectionTensorMap π (𝟙_ D) N) :=
    IsIso.of_isIso_comp_right _ (R.map (λ_ N).hom)
  exact IsIso.of_isIso_comp_left (adj.homEquiv _ _ t ▷ F.obj N) _

end CategoryTheory.Adjunction
