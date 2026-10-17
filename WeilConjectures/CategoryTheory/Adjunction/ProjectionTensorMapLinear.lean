/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# The tensor map of an adjunction with a linear counit

Let `adj : L ⊣ R` be an adjunction between monoidal categories with an invertible projection map
`π M N : L M ⊗ N ⟶ L (M ⊗ F N)` (a projection formula for a pullback `F`), and suppose that `L`
also has the right adjoint `N ↦ T ⊗ F N` for an object `T`, through an adjunction `adj'` whose
counit is *linear*: it is the inverse of the projection map followed by a morphism
`t : L T ⟶ 𝟙_`,

`ε'_N : L (T ⊗ F N) ≅ L T ⊗ N ⟶ 𝟙_ ⊗ N ≅ N`.

This is the shape of the projective-line adjunction `Rq_* ⊣ q^*(1)[2]`, whose counit is the
projection formula followed by the trace. Then the tensor map `τ (𝟙_) N : R 𝟙_ ⊗ F N ⟶ R N`
of `adj` (`CategoryTheory.Adjunction.projectionTensorMap`) is an isomorphism for every `N`, as
soon as the projection map is associative: for `adj'` it is the reassociation
`(T ⊗ F 𝟙_) ⊗ F N ≅ T ⊗ F (𝟙_ ⊗ N)`, and the tensor maps of `adj` and `adj'` agree through the
isomorphism of right adjoints.

## Main statements

- `CategoryTheory.Adjunction.projectionTensorMap_rightAdjointUniq`
- `CategoryTheory.Adjunction.isIso_projectionTensorMap_of_counit_eq`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

/-- The tensor maps of two adjunctions with the same left adjoint agree through the isomorphism
of right adjoints, if the projection map is natural in its first variable. -/
theorem projectionTensorMap_rightAdjointUniq
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    {R' : D ⥤ C} (adj' : L ⊣ R') (M N : D) :
    adj.projectionTensorMap π M N ≫ (adj.rightAdjointUniq adj').hom.app (M ⊗ N) =
      (adj.rightAdjointUniq adj').hom.app M ▷ F.obj N ≫ adj'.projectionTensorMap π M N := by
  apply ext_of_comp_counit (adj := adj')
  have h := hπ ((adj.rightAdjointUniq adj').hom.app M) N
  rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [Functor.map_comp, Category.assoc, rightAdjointUniq_hom_app_counit,
    map_projectionTensorMap_comp_counit, Functor.map_comp, Category.assoc,
    map_projectionTensorMap_comp_counit, ← reassoc_of% h, ← comp_whiskerRight,
    rightAdjointUniq_hom_app_counit]

/-- **The tensor map of an adjunction with a linear counit.** If `L` has a second right adjoint
`N ↦ T ⊗ F N` whose counit is the inverse of the projection map followed by `t : L T ⟶ 𝟙_` and
the left unitor, and the projection map is natural and associative (for a comparison
`δ : F (N ⊗ N') ≅ F N ⊗ F N'`), then the tensor map `τ (𝟙_) N : R 𝟙_ ⊗ F N ⟶ R N` of `adj` is an
isomorphism. -/
theorem isIso_projectionTensorMap_of_counit_eq
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (δ : ∀ N N' : D, F.obj (N ⊗ N') ⟶ F.obj N ⊗ F.obj N') [∀ N N', IsIso (δ N N')]
    (hassoc : ∀ (M : C) (N N' : D), π M N ▷ N' ≫ π (M ⊗ F.obj N) N' ≫
      L.map (α_ M (F.obj N) (F.obj N')).hom = (α_ _ N N').hom ≫ π M (N ⊗ N') ≫ L.map (M ◁ δ N N'))
    {T : C} (t : L.obj T ⟶ 𝟙_ D) (adj' : L ⊣ F ⋙ tensorLeft T)
    (hε : ∀ N : D, adj'.counit.app N = inv (π T N) ≫ t ▷ N ≫ (λ_ N).hom) (N : D) :
    IsIso (adj.projectionTensorMap π (𝟙_ D) N) := by
  -- the tensor map of `adj'` is the reassociation
  have h' : adj'.projectionTensorMap π (𝟙_ D) N =
      (α_ T (F.obj (𝟙_ D)) (F.obj N)).hom ≫ T ◁ inv (δ (𝟙_ D) N) := by
    apply ext_of_comp_counit (adj := adj')
    rw [map_projectionTensorMap_comp_counit, hε, hε]
    have h := hassoc T (𝟙_ D) N
    have h₂ : L.map (α_ T (F.obj (𝟙_ D)) (F.obj N)).hom ≫ L.map (T ◁ inv (δ (𝟙_ D) N)) ≫
        inv (π T (𝟙_ D ⊗ N)) =
        inv (π (T ⊗ F.obj (𝟙_ D)) N) ≫ inv (π T (𝟙_ D)) ▷ N ≫
          (α_ (L.obj T) (𝟙_ D) N).hom := by
      rw [← cancel_mono (π T (𝟙_ D ⊗ N)), ← cancel_mono (L.map (T ◁ δ (𝟙_ D) N))]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Functor.map_comp,
        ← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id]
      rw [← h]
      simp
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% h₂]
    simp only [comp_whiskerRight]
    congr 2
    rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom, Iso.hom_inv_id_assoc]
  -- transfer along the isomorphism of right adjoints
  have h := projectionTensorMap_rightAdjointUniq adj π hπ adj' (𝟙_ D) N
  have : IsIso (adj'.projectionTensorMap π (𝟙_ D) N) := by
    rw [h']
    infer_instance
  have : IsIso (adj.projectionTensorMap π (𝟙_ D) N ≫
      (adj.rightAdjointUniq adj').hom.app (𝟙_ D ⊗ N)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adj.rightAdjointUniq adj').hom.app (𝟙_ D ⊗ N))

end CategoryTheory.Adjunction
