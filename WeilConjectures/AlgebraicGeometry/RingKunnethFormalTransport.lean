/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Formal transport of a projection map through composite adjunctions
Source: Stacks Tag 0F1E, the composite adjunction calculation.
(blueprint: lem-sf-ring-kunneth-formal-projection-transport).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory.Adjunction

private theorem tensorComparisonNaturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    F.map (f ⊗ₘ g) ≫ (δ.app P').app Q' =
      (δ.app P).app Q ≫ (F.map f ⊗ₘ F.map g) := by
  have h₁ := congr_app (δ.naturality f) Q
  have h₂ := (δ.app P').naturality g
  dsimp at h₁ h₂
  simp only [tensorHom_def, Functor.map_comp, Category.assoc]
  rw [h₂, reassoc_of% h₁]

/-- Projection transport follows from tensor compatibility and conjugacy of the
specified comparison of right adjoints.
Source: Stacks Tag 0F1E (blueprint: lem-sf-ring-kunneth-formal-projection-transport).
Proof: postcompose with the right comparison and transpose under the final adjunction.
Conjugacy replaces this by the composite adjunction. Expand the projection adjunct and
the point tensor adjunct. Naturality moves the two point counits through the inverse-image
tensor comparison; tensor compatibility replaces the composite comparison by the final
one. Naturality moves the two inverse comparison maps through that final tensor. Conjugacy
and its counit equation cancel the first inverse right comparison, leaving the final
counit in the first tensor factor. The second factor is the displayed transported map.
The defining adjunct of the final projection map gives the result by injectivity. -/
theorem ringKunnethProjectionTransportFormal
    {C B D : Type*} [Category C] [Category B] [Category D]
    [MonoidalCategory C] [MonoidalCategory B] [MonoidalCategory D]
    {F : C ⥤ B} {R : B ⥤ C} {L : B ⥤ D} {S : D ⥤ B} {H : C ⥤ D} {T : D ⥤ C}
    (a₀ : F ⊣ R) (a₁ : L ⊣ S) (a₂ : H ⊣ T)
    (d : H ≅ F ⋙ L) (e : S ⋙ R ≅ T)
    (δ₀ : ∀ P Q : C, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (δ₁ : (Functor.postcompose₂.obj L).obj (curriedTensor B) ⟶
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj (curriedTensor D))
    (δ₂ : (Functor.postcompose₂.obj H).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj H).obj H).obj (curriedTensor D))
    (he : e.hom = conjugateEquiv (a₀.comp a₁) a₂ d.hom)
    (hd : ∀ P Q, d.hom.app (P ⊗ Q) ≫ L.map (δ₀ P Q) ≫
      (δ₁.app (F.obj P)).app (F.obj Q) =
        (δ₂.app P).app Q ≫ (d.hom.app P ⊗ₘ d.hom.app Q))
    (E : D) (N : B) (Q : C) (q : R.obj N ≅ Q) :
    (e.inv.app E ⊗ₘ q.inv) ≫
        a₀.homEquiv _ _ (δ₀ (R.obj (S.obj E)) (R.obj N) ≫
          (a₀.counit.app (S.obj E) ⊗ₘ a₀.counit.app N)) ≫
        R.map (((a₁.rightAdjointProjectionMap δ₁).app E).app N) =
      ((a₂.rightAdjointProjectionMap δ₂).app E).app Q ≫
        T.map (𝟙 E ⊗ₘ (H.map q.inv ≫ d.hom.app (R.obj N) ≫
          L.map (a₀.counit.app N))) ≫ e.inv.app _ := by
  have htr {P : C} {Z : D} (z : P ⟶ R.obj (S.obj Z)) :
      (a₂.homEquiv P Z).symm (z ≫ e.hom.app Z) =
        d.hom.app P ≫ ((a₀.comp a₁).homEquiv P Z).symm z := by
    rw [he, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc, conjugateEquiv_counit]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using
      congrArg (fun f ↦ f ≫ (a₀.comp a₁).counit.app Z) (d.hom.naturality z)
  have hc : H.map (e.inv.app E) ≫ d.hom.app (R.obj (S.obj E)) ≫
      L.map (a₀.counit.app (S.obj E)) ≫ a₁.counit.app E = a₂.counit.app E := by
    have h := conjugateEquiv_counit (a₀.comp a₁) a₂ d.hom E
    rw [← he] at h
    simp only [Adjunction.comp_counit_app, Functor.comp_obj, Functor.id_obj] at h
    rw [← h, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  apply (cancel_mono (e.hom.app (E ⊗ L.obj N))).1
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app e (E ⊗ L.obj N), Category.comp_id]
  apply (a₂.homEquiv _ _).symm.injective
  conv_lhs => rw [← Category.assoc, ← Category.assoc]
  rw [htr, Adjunction.comp_homEquiv]
  simp only [Category.assoc]
  change d.hom.app _ ≫ (a₁.homEquiv _ _).symm
    ((a₀.homEquiv _ _).symm (_ ≫ a₀.homEquiv _ _ _ ≫ R.map _)) = _
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
  rw [a₀.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    a₁.homEquiv_naturality_left_symm]
  erw [a₁.homEquiv_symm_rightAdjointProjectionMap_app_app δ₁ E N]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (tensorComparisonNaturality L δ₁
    (a₀.counit.app (S.obj E)) (a₀.counit.app N))]
  rw [← reassoc_of% (d.hom.naturality (e.inv.app E ⊗ₘ q.inv)),
    reassoc_of% (hd _ _),
    reassoc_of% (tensorComparisonNaturality H δ₂ (e.inv.app E) q.inv)]
  erw [a₂.homEquiv_naturality_right_symm,
    a₂.homEquiv_symm_rightAdjointProjectionMap_app_app δ₂ E Q]
  simp only [curriedTensor_map_app, ← tensorHom_id]
  change (δ₂.app (T.obj E)).app Q ≫
    (H.map (e.inv.app E) ⊗ₘ H.map q.inv) ≫
      (d.hom.app _ ⊗ₘ d.hom.app _) ≫
        (L.map (a₀.counit.app _) ⊗ₘ L.map (a₀.counit.app _)) ≫
          (a₁.counit.app E ⊗ₘ 𝟙 _) =
    ((δ₂.app (T.obj E)).app Q ≫ (a₂.counit.app E ⊗ₘ 𝟙 _)) ≫
      (𝟙 E ⊗ₘ (H.map q.inv ≫ d.hom.app _ ≫ L.map (a₀.counit.app N)))
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, Category.assoc]
  erw [hc]
  simp

end CategoryTheory.Adjunction
