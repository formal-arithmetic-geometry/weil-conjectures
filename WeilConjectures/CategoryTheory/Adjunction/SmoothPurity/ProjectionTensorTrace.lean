/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-! # Tensoring an arbitrary adjoint trace

Source: the projection-naturality calculation in the coefficient part of
`lem-pur-projection-purity-agreement`.
(blueprint: lem-pur-projection-tensor-trace)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

/-- Tensoring the adjunct of a trace and applying the canonical tensor mate gives
the adjunct of inverse projection followed by the tensor of that trace.

Source: the coefficient tensor calculation in
blueprint, sec-smooth-purity/sk-thm-smooth-purity,
`lem-pur-projection-purity-agreement.proof.md`.
(blueprint: lem-pur-projection-tensor-trace)

Proof: apply the inverse adjunction bijection. The defining counit equation for
the tensor mate leaves inverse projection and the counit. Naturality of inverse
projection moves the adjunct of the trace to the coefficient factor. The
adjunction triangle says its composite with the counit is the original trace.
Functoriality of tensor then gives the required equation. -/
theorem projectionTensorMap_trace
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)]
    (hπ : ∀ {M M' : C} (f : M ⟶ M') (N : D),
      L.map f ▷ N ≫ π M' N = π M N ≫ L.map (f ▷ F.obj N))
    {W : C} {M : D} (t : L.obj W ⟶ M) (N : D) :
    adj.homEquiv W M t ▷ F.obj N ≫ adj.projectionTensorMap π M N =
      adj.homEquiv _ _ (inv (π W N) ≫ t ▷ N) := by
  let q := adj.homEquiv W M t
  have hi : L.map (q ▷ F.obj N) ≫ inv (π (R.obj M) N) =
      inv (π W N) ≫ L.map q ▷ N := by
    apply (cancel_epi (π W N)).1
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc] using
      congrArg (fun z ↦ z ≫ inv (π (R.obj M) N)) (hπ q N).symm
  have hq : L.map q ≫ adj.counit.app M = t := by
    exact (adj.homEquiv _ _).symm_apply_apply t
  apply adj.ext_of_comp_counit
  rw [Functor.map_comp, Category.assoc, adj.map_projectionTensorMap_comp_counit]
  change L.map (q ▷ F.obj N) ≫ inv (π (R.obj M) N) ≫
      adj.counit.app M ▷ N = _
  rw [← Category.assoc, hi, Category.assoc, ← comp_whiskerRight, hq]
  exact ((adj.homEquiv _ _).symm_apply_apply _).symm


/-- The pullback-first tensor mate of a trace, with a specified unit comparison.

Source: projection purity agreement, coefficient tensor calculation.
(blueprint: lem-pur-projection-tensor-trace)

Proof: naturality of the adjunction absorbs the unit comparison into the trace.
Naturality of the braiding moves its adjunct to the first factor. Apply
projectionTensorMap_trace, then adjunction naturality for the left unitor and
for the source braiding. -/
theorem projectionTensorMap_unit_trace
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)]
    (hπ : ∀ {M M' : C} (f : M ⟶ M') (N : D),
      L.map f ▷ N ≫ π M' N = π M N ≫ L.map (f ▷ F.obj N))
    {W : C} {U : D} (t : L.obj W ⟶ U) (e : U ≅ 𝟙_ D) (N : D) :
    (F.obj N ◁ adj.homEquiv _ _ t) ≫ (F.obj N ◁ R.map e.hom) ≫
        (β_ _ _).hom ≫ adj.projectionTensorMap π (𝟙_ D) N ≫ R.map (λ_ N).hom =
      adj.homEquiv _ _
        (L.map (β_ (F.obj N) W).hom ≫ inv (π W N) ≫
          (t ≫ e.hom) ▷ N ≫ (λ_ N).hom) := by
  rw [← whiskerLeft_comp_assoc, ← adj.homEquiv_naturality_right]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [reassoc_of% (projectionTensorMap_trace adj π hπ (t ≫ e.hom) N)]
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
  simp only [Category.assoc]

end CategoryTheory.Adjunction
