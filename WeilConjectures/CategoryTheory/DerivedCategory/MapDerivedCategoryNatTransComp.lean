/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Induced natural transformations and composition of exact functors

Compatibility of `Functor.mapDerivedCategoryNatTrans` with the composition isomorphisms
`Functor.mapDerivedCategoryCompIso`
(`Functor.mapDerivedCategoryNatTrans_comp_mapDerivedCategoryCompIso`), together with the
descriptions of `Functor.mapDerivedCategoryCompIso` on the image of a complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section Composition

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` on the image of a complex
is compatible with the factorizations `Functor.mapDerivedCategoryFactors`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_Q_fac (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app K = 𝟙 _ := by
    ext
    rfl
  simpa [h] using mapDerivedCategoryCompIso_fac F G K

/-- The inverse of `Functor.mapDerivedCategoryCompIso` on the image of a complex, through the
factorizations `Functor.mapDerivedCategoryFactors`. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_inv_app_Q_fac (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  rw [← mapDerivedCategoryCompIso_hom_app_Q_fac, Iso.inv_hom_id_app_assoc]

/-- A variant of `Functor.mapDerivedCategoryCompIso_inv_app_Q_fac` after applying a further
exact functor `H`, stated so that the targets of both sides are syntactically the image of
the iterated levelwise application of `F` and `G`. -/
lemma mapDerivedCategory_map_mapDerivedCategoryCompIso_inv_app_Q_fac {E' : Type*} [Category E']
    [Abelian E'] [HasDerivedCategory E'] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.Additive]
    [G.Additive] [H.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : CochainComplex C ℤ) :
    H.mapDerivedCategory.map ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    H.mapDerivedCategory.map (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  rw [mapDerivedCategoryCompIso_inv_app_Q_fac]
  rfl

/-- Naturality of the factorization `Functor.mapDerivedCategoryFactors` with respect to a
morphism of complexes. -/
@[reassoc]
lemma mapDerivedCategory_map_Q_map_fac (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {K L : CochainComplex C ℤ}
    (f : K ⟶ L) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        F.mapDerivedCategoryFactors.hom.app L =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  F.mapDerivedCategoryFactors.hom.naturality f

end Composition

section Composite

variable {C₁ C₂ C₃ E : Type*} [Category C₁] [Category C₂] [Category C₃] [Category E]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian E]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] [HasDerivedCategory E]
  {P₁₂ : C₁ ⥤ C₂} {P₂₃ : C₂ ⥤ C₃} {P₁₃ : C₁ ⥤ C₃} {Γ₁ : C₁ ⥤ E} {Γ₂ : C₂ ⥤ E} {Γ₃ : C₃ ⥤ E}
  [P₁₂.Additive] [PreservesFiniteLimits P₁₂] [PreservesFiniteColimits P₁₂]
  [P₂₃.Additive] [PreservesFiniteLimits P₂₃] [PreservesFiniteColimits P₂₃]
  [P₁₃.Additive] [PreservesFiniteLimits P₁₃] [PreservesFiniteColimits P₁₃]
  [Γ₁.Additive] [PreservesFiniteLimits Γ₁] [PreservesFiniteColimits Γ₁]
  [Γ₂.Additive] [PreservesFiniteLimits Γ₂] [PreservesFiniteColimits Γ₂]
  [Γ₃.Additive] [PreservesFiniteLimits Γ₃] [PreservesFiniteColimits Γ₃]

/-- Natural transformations `τ₁₂ : Γ₁ ⟶ P₁₂ ⋙ Γ₂`, `τ₂₃ : Γ₂ ⟶ P₂₃ ⋙ Γ₃` and
`τ₁₃ : Γ₁ ⟶ P₁₃ ⋙ Γ₃` of exact functors which are compatible with an isomorphism
`P₁₃ ≅ P₁₂ ⋙ P₂₃` induce compatible natural transformations on derived categories, once
composed with the composition isomorphisms `Functor.mapDerivedCategoryCompIso`. -/
lemma mapDerivedCategoryNatTrans_comp_mapDerivedCategoryCompIso
    (e : P₁₃ ≅ P₁₂ ⋙ P₂₃) (τ₁₂ : Γ₁ ⟶ P₁₂ ⋙ Γ₂) (τ₂₃ : Γ₂ ⟶ P₂₃ ⋙ Γ₃)
    (τ₁₃ : Γ₁ ⟶ P₁₃ ⋙ Γ₃)
    (hτ : ∀ X, τ₁₃.app X ≫ Γ₃.map (e.hom.app X) = τ₁₂.app X ≫ τ₂₃.app (P₁₂.obj X)) :
    mapDerivedCategoryNatTrans τ₁₃ ≫ (mapDerivedCategoryCompIso P₁₃ Γ₃).hom ≫
        whiskerRight (mapDerivedCategoryNatIso e).hom Γ₃.mapDerivedCategory =
      mapDerivedCategoryNatTrans τ₁₂ ≫ (mapDerivedCategoryCompIso P₁₂ Γ₂).hom ≫
        whiskerLeft P₁₂.mapDerivedCategory
          (mapDerivedCategoryNatTrans τ₂₃ ≫ (mapDerivedCategoryCompIso P₂₃ Γ₃).hom) ≫
        whiskerRight (mapDerivedCategoryCompIso P₁₂ P₂₃).inv Γ₃.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) (fun K => ?_)
  rw [← cancel_mono (Γ₃.mapDerivedCategory.map
      ((P₁₂ ⋙ P₂₃).mapDerivedCategoryFactors.hom.app K) ≫
    Γ₃.mapDerivedCategoryFactors.hom.app
      (((P₁₂ ⋙ P₂₃).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Category.assoc]
  rw [← Functor.map_comp_assoc, mapDerivedCategoryNatIso_fac, Functor.map_comp_assoc,
    mapDerivedCategory_map_Q_map_fac, mapDerivedCategoryCompIso_hom_app_Q_fac_assoc,
    mapDerivedCategoryNatTrans_fac_assoc, ← Functor.map_comp_assoc,
    mapDerivedCategory_map_mapDerivedCategoryCompIso_inv_app_Q_fac, Functor.map_comp_assoc]
  rw [← Functor.comp_map P₂₃.mapDerivedCategory Γ₃.mapDerivedCategory,
    ← (mapDerivedCategoryCompIso P₂₃ Γ₃).hom.naturality_assoc,
    ← (mapDerivedCategoryNatTrans τ₂₃).naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [mapDerivedCategoryCompIso_hom_app_Q_fac, mapDerivedCategoryNatTrans_fac,
    mapDerivedCategoryCompIso_hom_app_Q_fac_assoc, mapDerivedCategoryNatTrans_fac_assoc,
    ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  ext i
  exact hτ (K.X i)

end Composite

end CategoryTheory.Functor
