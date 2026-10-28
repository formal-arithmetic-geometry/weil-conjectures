/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTransAdditive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Traces of derived adjunctions of exact functors

Let `adj : f ⊣ g` be an adjunction of exact functors between abelian categories, and let
`t : f ⋙ g ⟶ 𝟭` be a *trace* with `u ≫ t = d • 𝟙` for the unit `u`, and `ρ i : f ⋙ g ⟶ f ⋙ g`
finitely many natural transformations with `t ≫ u = ∑ i, ρ i`. Then the derived adjunction
`Lf ⊣ Rg` (`CategoryTheory.Adjunction.derivedAdjunction`) carries a trace and endomorphisms
satisfying the same identities (`CategoryTheory.Adjunction.unit_comp_derivedTrace`,
`CategoryTheory.Adjunction.derivedTrace_comp_unit`).

The unit of the levelwise derived adjunction `D(f) ⊣ D(g)` is the levelwise unit
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_eq`), and the derived adjunction
differs from it by the isomorphisms `Lf ≅ D(f)`, `Rg ≅ D(g)`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The unit of the levelwise derived adjunction `D(f) ⊣ D(g)` is the levelwise unit. -/
lemma mapDerivedCategoryAdjunction_unit_eq :
    adj.mapDerivedCategoryAdjunction.unit =
      (Functor.mapDerivedCategoryIdIso C).inv ≫ Functor.mapDerivedCategoryNatTrans adj.unit ≫
        (Functor.mapDerivedCategoryCompIso f g).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun Y ↦ ?_
  have hu := adj.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y)
  rw [mapHomotopyCategory_unit_app_quotient] at hu
  have hc := Functor.mapDerivedCategoryCompIso_fac f g Y
  have hn := Functor.mapDerivedCategoryNatTrans_fac adj.unit Y
  have hi := congr_app (congr_arg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y)
  have hu' : adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj Y) ≫
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app Y) ≫
        g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex _).obj Y) =
      DerivedCategory.Q.map ((mapHomologicalComplex (ComplexShape.up ℤ) adj).unit.app Y) := by
    have e1 : (DerivedCategory.quotientCompQhIso C).hom.app Y = 𝟙 _ := rfl
    have e2 : (DerivedCategory.quotientCompQhIso D).inv.app ((f.mapHomologicalComplex _).obj Y) =
      𝟙 _ := rfl
    have e3 : (f.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app Y = 𝟙 _ := rfl
    have e4 := g.mapDerivedCategoryFactorsh_hom_app ((f.mapHomologicalComplex _).obj Y)
    have e5 : (DerivedCategory.quotientCompQhIso D).hom.app ((f.mapHomologicalComplex _).obj Y) =
      𝟙 _ := rfl
    have e6 : (DerivedCategory.quotientCompQhIso C).inv.app ((g.mapHomologicalComplex _).obj
      ((f.mapHomologicalComplex _).obj Y)) = 𝟙 _ := rfl
    have e7 : (g.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      ((f.mapHomologicalComplex _).obj Y) = 𝟙 _ := rfl
    simp only [e5, e6, e7, Functor.map_id, id_comp] at e4
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app, e1, e2, e3, Functor.map_id,
      id_comp] at hu
    erw [e4] at hu
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_id, comp_id] at hu
    exact hu
  have hi' : (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj Y) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app Y ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom.app Y) := by
    simp only [Functor.mapDerivedCategoryFactorsh_hom_app, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hi
    have e1 : (DerivedCategory.quotientCompQhIso C).hom.app Y = 𝟙 _ := rfl
    have e3 : ((𝟭 C).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app Y = 𝟙 _ := rfl
    have e4 : (DerivedCategory.quotientCompQhIso C).inv.app
      (((𝟭 C).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) = 𝟙 _ := rfl
    simp only [e1, e3, CategoryTheory.Functor.map_id, Category.id_comp] at hi
    simp only [e4] at hi
    simp only [Functor.comp_obj, Functor.id_obj, comp_id, Functor.map_id,
      Functor.mapHomotopyCategoryIdIso_hom_app] at hi
    exact hi
  rw [← cancel_mono (g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app Y) ≫
    g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex _).obj Y) ≫
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (f ⋙ g))
      (ComplexShape.up ℤ)).hom.app Y)), reassoc_of% hu']
  simp only [NatTrans.comp_app, assoc]
  rw [hc, hn, ← cancel_epi ((Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj Y)),
    Iso.hom_inv_id_app_assoc, hi', assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext n
  simp only [Functor.id_obj, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f,
    mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, id_comp, NatTrans.mapHomologicalComplex_app_f]
  exact comp_id _

end CategoryTheory.Adjunction
