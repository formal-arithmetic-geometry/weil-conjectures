/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemScalarPullbackGeneralMate
public import WeilConjectures.CategoryTheory.Adjunction.NormalizedExactDerivedUnit
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Mates and inverses of localized squares

For exact adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` between abelian categories, the mate of the
localization of a square is the localization of its mate, and the localizations of mutually
inverse squares are mutually inverse.

## References

* Stacks Project, Tags 05RS and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

section DerivedMate

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂}
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁] [PreservesFiniteLimits L₂]
  [PreservesFiniteColimits L₂] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits H]
  [PreservesFiniteColimits H] in
/-- The cochain form of the unit equation of a mate. -/
private theorem cochain_unit_mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (P : CochainComplex C₁ ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj₁.unit (.up ℤ)).app P) ≫
      (NatTrans.mapHomologicalComplex (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α))
        (.up ℤ)).app ((L₁.mapHomologicalComplex (.up ℤ)).obj P) =
    (NatTrans.mapHomologicalComplex adj₂.unit (.up ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (R₂.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := by
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  exact unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) (P.X n)

/-- The mate along localized exact adjunctions of a localized square is the localization
of the ordinary mate. -/
theorem isDerivedSquareOf_mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    {Δα : G.mapDerivedCategory ⋙ L₂.mapDerivedCategory ⟶
      L₁.mapDerivedCategory ⋙ H.mapDerivedCategory} (hα : IsDerivedSquareOf α Δα) :
    IsDerivedSquareOf (F₁ := R₁) (F₂ := G) (F₃ := H) (F₄ := R₂)
      (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α))
      (mateEquiv adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
        (TwoSquare.mk _ _ _ _ Δα)) := by
  obtain ⟨Δβ, hβ⟩ := exists_isDerivedSquareOf (F₁ := R₁) (F₂ := G) (F₃ := H) (F₄ := R₂)
    (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α))
  suffices e : Δβ = mateEquiv adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
      (TwoSquare.mk _ _ _ _ Δα) by
    rw [← e]
    exact hβ
  refine (mateEquiv_eq_of_unit _ _ _ _ ?_).symm
  have key : (Functor.whiskerRight adj₁.mapExactDerivedCategory.unit G.mapDerivedCategory ≫
      Functor.whiskerLeft L₁.mapDerivedCategory Δβ : G.mapDerivedCategory ⟶
        L₁.mapDerivedCategory ⋙ H.mapDerivedCategory ⋙ R₂.mapDerivedCategory) =
      Functor.whiskerLeft G.mapDerivedCategory adj₂.mapExactDerivedCategory.unit ≫
        Functor.whiskerRight Δα R₂.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (.up ℤ))
    intro P
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (R₂.mapDerivedCategory.map (H.mapDerivedCategory.map
        (L₁.mapDerivedCategoryFactors.hom.app P)) ≫
      R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj
        ((L₁.mapHomologicalComplex (.up ℤ)).obj P)))]
    simp only [Category.assoc]
    have n1 := Δβ.naturality (L₁.mapDerivedCategoryFactors.hom.app P)
    have n2 : G.mapDerivedCategory.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj₁.unit (.up ℤ)).app P)) ≫
        G.mapDerivedCategoryFactors.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj
          ((L₁.mapHomologicalComplex (.up ℤ)).obj P)) =
      G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adj₁.unit (.up ℤ)).app P)) :=
      G.mapDerivedCategoryFactors.hom.naturality _
    have n3 := adj₂.mapExactDerivedCategory.unit.naturality
      (G.mapDerivedCategoryFactors.hom.app P)
    have n4 : R₂.mapDerivedCategory.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P)) ≫
        R₂.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj
          ((L₁.mapHomologicalComplex (.up ℤ)).obj P)) =
      R₂.mapDerivedCategoryFactors.hom.app ((L₂.mapHomologicalComplex (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫ DerivedCategory.Q.map
        ((R₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P)) :=
      R₂.mapDerivedCategoryFactors.hom.naturality _
    simp only [Functor.comp_map, Functor.id_map] at n1 n3
    have u1 := adj₁.mapExactDerivedCategory_unit P
    have u2 := adj₂.mapExactDerivedCategory_unit ((G.mapHomologicalComplex (.up ℤ)).obj P)
    rw [← reassoc_of% n1, hβ, ← G.mapDerivedCategory.map_comp_assoc,
      ← G.mapDerivedCategory.map_comp_assoc, Category.assoc, u1, reassoc_of% n2,
      ← R₂.mapDerivedCategory.map_comp_assoc, ← R₂.mapDerivedCategory.map_comp_assoc,
      Category.assoc, hα P, R₂.mapDerivedCategory.map_comp,
      R₂.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% n3, n4,
      reassoc_of% u2, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
      cochain_unit_mateEquiv]
  intro X
  simpa using congr_app key X

end DerivedMate

/-- Localized squares of mutually inverse ordinary squares are inverse. -/
theorem isDerivedSquareOf_comp_eq_id {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {F₃ : A ⥤ C} {F₄ : C ⥤ D}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
    [F₄.Additive] [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]
    {σ : F₁ ⋙ F₂ ⟶ F₃ ⋙ F₄} {τ : F₃ ⋙ F₄ ⟶ F₁ ⋙ F₂} (h : σ ≫ τ = 𝟙 _)
    {Δ : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ⟶
      F₃.mapDerivedCategory ⋙ F₄.mapDerivedCategory}
    {Δ' : F₃.mapDerivedCategory ⋙ F₄.mapDerivedCategory ⟶
      F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory}
    (hΔ : IsDerivedSquareOf σ Δ) (hΔ' : IsDerivedSquareOf τ Δ') :
    Δ ≫ Δ' = 𝟙 _ := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro P
  have hP : (NatTrans.mapHomologicalComplex σ (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P = 𝟙 _ := by
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.id_f]
    exact congr_app h (P.X n)
  rw [NatTrans.comp_app, NatTrans.id_app, ← cancel_mono
    (F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)),
    Category.assoc, hΔ' P, reassoc_of% (hΔ P), ← DerivedCategory.Q.map_comp, hP]
  erw [DerivedCategory.Q.map_id, Category.comp_id, Category.id_comp]

end CategoryTheory.Functor
