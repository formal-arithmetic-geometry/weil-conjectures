/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!
# Tensor maps of linear adjunctions

Let `adj : L ⊣ R` be an adjunction with a projection map `π M N : L M ⊗ N ⟶ L (M ⊗ F N)`, and
let `τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` be its tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`). This file records three formal facts:

* the tensor map does not depend on the choice of the right adjoint: two right adjoints of `L`
  have the same tensor maps through `CategoryTheory.Adjunction.rightAdjointUniq`
  (`CategoryTheory.Adjunction.projectionTensorMap_rightAdjointUniq_hom`);
* if the right adjoint is `F` itself and the unit of `L ⊣ F` is compatible with the projection map
  and a tensor comparison `μ : F (A ⊗ B) ≅ F A ⊗ F B`, then the tensor map is `μ⁻¹`
  (`CategoryTheory.Adjunction.projectionTensorMap_eq_of_unit`);
* if the counit at `N` is the projection map followed by the counit at `𝟙_` tensored with `N`,
  through an isomorphism `R 𝟙_ ⊗ F N ≅ R N`, then the tensor map at `(𝟙_, N)` is an isomorphism
  (`CategoryTheory.Adjunction.isIso_projectionTensorMap_unit_of_counit`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D}
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]

section Uniq

variable {R R' : D ⥤ C} (adj : L ⊣ R) (adj' : L ⊣ R')

/-- **The tensor map does not depend on the right adjoint**: through the isomorphism
`ρ : R ≅ R'` of two right adjoints of `L`, the tensor maps of `L ⊣ R` and `L ⊣ R'` agree. -/
@[reassoc]
lemma projectionTensorMap_rightAdjointUniq_hom
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (M N : D) :
    adj.projectionTensorMap π M N ≫ (rightAdjointUniq adj adj').hom.app (M ⊗ N) =
      (rightAdjointUniq adj adj').hom.app M ▷ F.obj N ≫ adj'.projectionTensorMap π M N := by
  apply ext_of_comp_counit (adj := adj')
  have h := hπ ((rightAdjointUniq adj adj').hom.app M) N
  rw [← cancel_epi (inv (π _ N)), ← cancel_mono (inv (π _ N))] at h
  simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  rw [Functor.map_comp, Category.assoc, rightAdjointUniq_hom_app_counit,
    map_projectionTensorMap_comp_counit, Functor.map_comp, Category.assoc,
    map_projectionTensorMap_comp_counit, ← reassoc_of% h, ← comp_whiskerRight,
    rightAdjointUniq_hom_app_counit]

/-- The tensor map of `L ⊣ R` is an isomorphism if and only if that of `L ⊣ R'` is. -/
lemma isIso_projectionTensorMap_iff_of_adjunction
    (hπ : ∀ {M M' : C} (φ : M ⟶ M') (N : D), L.map φ ▷ N ≫ π M' N = π M N ≫ L.map (φ ▷ F.obj N))
    (M N : D) :
    IsIso (adj.projectionTensorMap π M N) ↔ IsIso (adj'.projectionTensorMap π M N) := by
  have h := projectionTensorMap_rightAdjointUniq_hom π adj adj' hπ M N
  constructor
  · intro
    have : IsIso ((rightAdjointUniq adj adj').hom.app M ▷ F.obj N ≫
        adj'.projectionTensorMap π M N) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((rightAdjointUniq adj adj').hom.app M ▷ F.obj N) _
  · intro
    have : IsIso (adj.projectionTensorMap π M N ≫
        (rightAdjointUniq adj adj').hom.app (M ⊗ N)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((rightAdjointUniq adj adj').hom.app (M ⊗ N))

end Uniq

section Unit

variable (adj : L ⊣ F) (μ : ∀ A B : D, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)

/-- **The tensor map of a linear adjunction `L ⊣ F`.** If the unit of `L ⊣ F` is compatible with
the projection map and a tensor comparison `μ : F (A ⊗ B) ≅ F A ⊗ F B` natural in `A`,
```
η_{M ⊗ F N} = (η_M ▷ F N) ≫ μ⁻¹ ≫ F (π M N),
```
then the tensor map `F M ⊗ F N ⟶ F (M ⊗ N)` is `μ⁻¹`. -/
theorem projectionTensorMap_eq_of_unit
    (hμ : ∀ {A A' : D} (φ : A ⟶ A') (B : D),
      F.map (φ ▷ B) ≫ (μ A' B).hom = (μ A B).hom ≫ F.map φ ▷ F.obj B)
    (h : ∀ (M : C) (N : D), adj.unit.app (M ⊗ F.obj N) =
      adj.unit.app M ▷ F.obj N ≫ (μ (L.obj M) N).inv ≫ F.map (π M N))
    (M N : D) :
    adj.projectionTensorMap π M N = (μ M N).inv := by
  have hμ' : (μ (L.obj (F.obj M)) N).inv ≫ F.map (adj.counit.app M ▷ N) =
      F.map (adj.counit.app M) ▷ F.obj N ≫ (μ M N).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% (hμ (adj.counit.app M) N), Iso.hom_inv_id,
      Category.comp_id]
  rw [projectionTensorMap, homEquiv_unit, h, Category.assoc, Category.assoc, ← F.map_comp,
    IsIso.hom_inv_id_assoc, hμ', ← comp_whiskerRight_assoc, right_triangle_components]
  simp

/-- The tensor map of a linear adjunction `L ⊣ F` is an isomorphism. -/
theorem isIso_projectionTensorMap_of_unit
    (hμ : ∀ {A A' : D} (φ : A ⟶ A') (B : D),
      F.map (φ ▷ B) ≫ (μ A' B).hom = (μ A B).hom ≫ F.map φ ▷ F.obj B)
    (h : ∀ (M : C) (N : D), adj.unit.app (M ⊗ F.obj N) =
      adj.unit.app M ▷ F.obj N ≫ (μ (L.obj M) N).inv ≫ F.map (π M N))
    (M N : D) :
    IsIso (adj.projectionTensorMap π M N) := by
  rw [projectionTensorMap_eq_of_unit π adj μ hμ h]
  infer_instance

end Unit

section Counit

variable {R : D ⥤ C} (adj : L ⊣ R)

/-- **The tensor map of an adjunction with linear counit.** If, through an isomorphism
`σ N : R 𝟙_ ⊗ F N ≅ R N`, the counit at `N` is the inverse of the projection map followed by the
counit at `𝟙_` tensored with `N` and the left unitor,
```
L (σ N) ≫ ε_N = π⁻¹ ≫ (ε_𝟙 ▷ N) ≫ λ_N,
```
then the tensor map at `(𝟙_, N)` followed by `R λ_N` is `σ N`, an isomorphism. -/
theorem projectionTensorMap_unit_comp_eq_of_counit (σ : ∀ N : D, R.obj (𝟙_ D) ⊗ F.obj N ≅ R.obj N)
    (h : ∀ N : D, L.map (σ N).hom ≫ adj.counit.app N =
      inv (π (R.obj (𝟙_ D)) N) ≫ adj.counit.app (𝟙_ D) ▷ N ≫ (λ_ N).hom)
    (N : D) :
    adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom = (σ N).hom := by
  apply ext_of_comp_counit (adj := adj)
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [map_projectionTensorMap_comp_counit_assoc, h]

/-- The tensor map at `(𝟙_, N)` of an adjunction with linear counit is an isomorphism. -/
theorem isIso_projectionTensorMap_unit_of_counit (σ : ∀ N : D, R.obj (𝟙_ D) ⊗ F.obj N ≅ R.obj N)
    (h : ∀ N : D, L.map (σ N).hom ≫ adj.counit.app N =
      inv (π (R.obj (𝟙_ D)) N) ≫ adj.counit.app (𝟙_ D) ▷ N ≫ (λ_ N).hom)
    (N : D) :
    IsIso (adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom) := by
  rw [projectionTensorMap_unit_comp_eq_of_counit π adj σ h]
  infer_instance

end Counit

end CategoryTheory.Adjunction
