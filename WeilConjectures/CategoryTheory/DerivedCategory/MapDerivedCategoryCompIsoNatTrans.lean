/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Natural transformations of exact functors and the derived compositor

For natural transformations between composites of exact functors, the induced transformations
of derived functors are compatible with `Functor.mapDerivedCategoryCompIso`: an identity
`σ ≫ Γ₂ μ = σ₁ ≫ σ₂ P₁` between the underived transformations holds after passing to derived
categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section CompIsoNatTrans

variable {S₀ S₁ S₂ E : Type*} [Category S₀] [Category S₁] [Category S₂] [Category E]
  [Abelian S₀] [Abelian S₁] [Abelian S₂] [Abelian E]
  [HasDerivedCategory S₀] [HasDerivedCategory S₁] [HasDerivedCategory S₂] [HasDerivedCategory E]

/-- On the image of a complex, a natural transformation `τ : H ⟶ F ⋙ G` of exact functors,
read on derived categories through `Functor.mapDerivedCategoryCompIso`, is the levelwise
image of `τ`. -/
@[reassoc]
lemma mapDerivedCategoryNatTrans_app_comp_compIso_hom_app_factors {H : S₀ ⥤ E} {F : S₀ ⥤ S₁}
    {G : S₁ ⥤ E} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : H ⟶ F ⋙ G) (K : CochainComplex S₀ ℤ) :
    (mapDerivedCategoryNatTrans τ).app (DerivedCategory.Q.obj K) ≫
        (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
  rw [mapDerivedCategoryCompIso_hom_app_factors]
  exact mapDerivedCategoryNatTrans_fac τ K

/-- On the image of a complex, an isomorphism `μ : H ≅ F ⋙ G` of exact functors, read on
derived categories through `Functor.mapDerivedCategoryCompIso`, is the levelwise image of
`μ`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_hom_app_comp_compIso_hom_app_factors {H : S₀ ⥤ E}
    {F : S₀ ⥤ S₁} {G : S₁ ⥤ E} [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (μ : H ≅ F ⋙ G) (K : CochainComplex S₀ ℤ) :
    (mapDerivedCategoryNatIso μ).hom.app (DerivedCategory.Q.obj K) ≫
        (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex μ.hom (ComplexShape.up ℤ)).app K) := by
  rw [mapDerivedCategoryCompIso_hom_app_factors]
  exact mapDerivedCategoryNatIso_fac μ K

variable {Γ₀ : S₀ ⥤ E} {Γ₁ : S₁ ⥤ E} {Γ₂ : S₂ ⥤ E} {P₁ : S₀ ⥤ S₁} {P₂ : S₁ ⥤ S₂}
  {P : S₀ ⥤ S₂} [Γ₀.Additive] [PreservesFiniteLimits Γ₀] [PreservesFiniteColimits Γ₀]
  [Γ₁.Additive] [PreservesFiniteLimits Γ₁] [PreservesFiniteColimits Γ₁]
  [Γ₂.Additive] [PreservesFiniteLimits Γ₂] [PreservesFiniteColimits Γ₂]
  [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Exact localization of a composition identity `σ ≫ Γ₂ μ = σ₁ ≫ σ₂ P₁` of natural
transformations `σ : Γ₀ ⟶ P ⋙ Γ₂`, `σ₁ : Γ₀ ⟶ P₁ ⋙ Γ₁`, `σ₂ : Γ₁ ⟶ P₂ ⋙ Γ₂` along an
isomorphism `μ : P ≅ P₁ ⋙ P₂` of exact functors: the induced natural transformations on
derived categories, read through `Functor.mapDerivedCategoryCompIso`, satisfy the same
identity. -/
lemma mapDerivedCategoryNatTrans_comp_compIso_hom_eq (σ : Γ₀ ⟶ P ⋙ Γ₂) (σ₁ : Γ₀ ⟶ P₁ ⋙ Γ₁)
    (σ₂ : Γ₁ ⟶ P₂ ⋙ Γ₂) (μ : P ≅ P₁ ⋙ P₂)
    (hσ : ∀ X, σ.app X ≫ Γ₂.map (μ.hom.app X) = σ₁.app X ≫ σ₂.app (P₁.obj X)) :
    mapDerivedCategoryNatTrans σ ≫ (mapDerivedCategoryCompIso P Γ₂).hom ≫
        Functor.whiskerRight ((mapDerivedCategoryNatIso μ).hom ≫
          (mapDerivedCategoryCompIso P₁ P₂).hom) Γ₂.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom =
      mapDerivedCategoryNatTrans σ₁ ≫ (mapDerivedCategoryCompIso P₁ Γ₁).hom ≫
        Functor.whiskerLeft P₁.mapDerivedCategory
          (mapDerivedCategoryNatTrans σ₂ ≫ (mapDerivedCategoryCompIso P₂ Γ₂).hom) := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso S₀ (ComplexShape.up ℤ)) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id]
  rw [← cancel_mono (Γ₂.mapDerivedCategory.map
      (P₂.mapDerivedCategory.map (P₁.mapDerivedCategoryFactors.hom.app K)) ≫
    Γ₂.mapDerivedCategory.map
      (P₂.mapDerivedCategoryFactors.hom.app
        ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    Γ₂.mapDerivedCategoryFactors.hom.app ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))]
  have hn := (mapDerivedCategoryNatTrans σ₂ ≫ (mapDerivedCategoryCompIso P₂ Γ₂).hom).naturality
    (P₁.mapDerivedCategoryFactors.hom.app K)
  simp only [NatTrans.comp_app, Functor.comp_map, Category.assoc] at hn
  trans Γ₀.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex σ₁ (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex σ₂ (ComplexShape.up ℤ)).app
        ((P₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  · rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, Category.assoc,
      mapDerivedCategoryNatIso_hom_app_comp_compIso_hom_app_factors, Functor.map_comp_assoc]
    erw [mapDerivedCategoryFactors_hom_naturality]
    rw [mapDerivedCategoryNatTrans_app_comp_compIso_hom_app_factors_assoc, ← Functor.map_comp]
    congr 2
    ext n
    exact hσ (K.X n)
  · simp only [Category.assoc]
    rw [← reassoc_of% hn, mapDerivedCategoryNatTrans_app_comp_compIso_hom_app_factors,
      mapDerivedCategoryNatTrans_app_comp_compIso_hom_app_factors_assoc, Functor.map_comp]

/-- Componentwise form of `Functor.mapDerivedCategoryNatTrans_comp_compIso_hom_eq`. -/
lemma mapDerivedCategoryNatTrans_comp_compIso_hom_app_eq (σ : Γ₀ ⟶ P ⋙ Γ₂)
    (σ₁ : Γ₀ ⟶ P₁ ⋙ Γ₁) (σ₂ : Γ₁ ⟶ P₂ ⋙ Γ₂) (μ : P ≅ P₁ ⋙ P₂)
    (hσ : ∀ X, σ.app X ≫ Γ₂.map (μ.hom.app X) = σ₁.app X ≫ σ₂.app (P₁.obj X))
    (M : DerivedCategory S₀) :
    (mapDerivedCategoryNatTrans σ).app M ≫ (mapDerivedCategoryCompIso P Γ₂).hom.app M ≫
        Γ₂.mapDerivedCategory.map ((mapDerivedCategoryNatIso μ).hom.app M) ≫
        Γ₂.mapDerivedCategory.map ((mapDerivedCategoryCompIso P₁ P₂).hom.app M) =
      (mapDerivedCategoryNatTrans σ₁).app M ≫ (mapDerivedCategoryCompIso P₁ Γ₁).hom.app M ≫
        (mapDerivedCategoryNatTrans σ₂).app (P₁.mapDerivedCategory.obj M) ≫
        (mapDerivedCategoryCompIso P₂ Γ₂).hom.app (P₁.mapDerivedCategory.obj M) := by
  simpa using NatTrans.congr_app (mapDerivedCategoryNatTrans_comp_compIso_hom_eq σ σ₁ σ₂ μ hσ) M

end CompIsoNatTrans

end CategoryTheory.Functor
