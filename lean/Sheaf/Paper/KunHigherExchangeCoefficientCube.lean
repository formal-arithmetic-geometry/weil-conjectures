/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# Higher exchange under a morphism of squares and coefficients

Source: Stacks Project, etale-cohomology.tex, Tags 0EYM and 0EZT, the construction of
transition maps and the final comparison, respectively
(blueprint: lem-kun-higher-exchange-coefficient-cube).
-/

@[expose] public section

open CategoryTheory Limits
-- Avoid costly conversion between the two category instances on derived categories.
attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace Comparisons
open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma mapHomologyIso_comp (S : ShortComplex C) :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (S.homologyData.left.map F) G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change ((S.homologyData.left.map F).map G).homologyIso.hom ≫
    G.map (S.mapHomologyIso F).inv ≫ G.map (S.mapHomologyIso F).hom = _
  simp only [← G.map_comp, Iso.inv_hom_id, G.map_id]
  change ((S.homologyData.left.map F).map G).homologyIso.hom ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change ((S.homologyData.left.map F).map G).homologyIso.hom =
    (S.homologyData.left.map (F ⋙ G)).homologyIso.hom
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      ((S.homologyData.left.map F).map G) (S.homologyData.left.map (F ⋙ G)) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp
      commf' := by simp
      commπ := by simp }
  have hγ := γ.homologyMap_comm
  simpa [γ] using hγ.symm

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma complex_homology_comp (n : ℤ) (L : CochainComplex C ℤ) :
    (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
      G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L) =
    ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L := by
  simp only [Functor.mapHomologicalComplexHomologyIso_hom_app_eq]
  convert mapHomologyIso_comp F G (L.sc n) using 1 <;> rfl

private lemma homology_comp (n : ℤ) (K : DerivedCategory C) :
    G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) =
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
      (DerivedCategory.homologyFunctor E n).map
        ((Functor.mapDerivedCategoryCompIso F G).hom.app K) := by
  have h : Functor.whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (G.mapDerivedCategoryHomologyFunctorIso n).hom =
      ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).hom
          (DerivedCategory.homologyFunctor E n) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro L
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
      (F.mapDerivedCategoryFactors.inv.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    simp only [hn]
    rw [G.mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      (F ⋙ G).mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Category.assoc]
    simp only [← G.map_comp_assoc, Iso.inv_hom_id_app]
    simp only [G.map_comp]
    have hc := complex_homology_comp F G n L
    have hci : G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app L) ≫
        (G.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj L) =
        ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app L := by
      apply (cancel_mono
        (((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L)).1
      rw [← hc]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app]
      erw [G.map_id]
      rw [hc, Iso.inv_hom_id_app]
      rfl
    have hi : (F ⋙ G).mapDerivedCategoryFactors.inv.app L ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj L) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L) := by
      simp only [comp_obj, mapDerivedCategoryCompIso, Localization.liftNatIso,
        Iso.refl_hom, Iso.refl_inv, Localization.liftNatTrans_app, NatTrans.id_app,
        Iso.trans_inv, isoWhiskerRight_inv, Iso.symm_inv, isoWhiskerLeft_inv,
        Category.assoc, NatTrans.comp_app, whiskerRight_app, associator_hom_app,
        whiskerLeft_app, associator_inv_app, Category.comp_id, Category.id_comp]
      change _ ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app L ≫ _ = _
      rw [Iso.inv_hom_id_app_assoc]
      have hId : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (.up ℤ)).inv.app L = 𝟙 _ := rfl
      rw [hId]
      erw [DerivedCategory.Q.map_id]
      rw [Category.id_comp]
    have him := congrArg (DerivedCategory.homologyFunctor E n).map hi
    simp only [Functor.map_comp] at him
    rw [him]
    dsimp only [Functor.comp_map, Functor.comp_obj] at *
    erw [G.map_id]
    simp only [Category.comp_id, Category.assoc]
    congr 1
    rw [← Category.assoc, hci]
    rfl
  exact NatTrans.congr_app h K

private lemma plus_homology_comp (n : ℤ) (K : DerivedCategory.Plus C) :
    G.map ((F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
      (G.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        (F.mapDerivedCategoryPlus.obj K) =
    ((F ⋙ G).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
      (DerivedCategory.Plus.homologyFunctor E n).map
        ((Functor.mapDerivedCategoryPlusCompIso F G).hom.app K) := by
  have h := homology_comp F G n (DerivedCategory.Plus.ι.obj K)
  dsimp [Functor.mapDerivedCategoryPlusHomologyFunctorIso,
    Functor.mapDerivedCategoryPlusCompatibility, DerivedCategory.Plus.homologyFunctor,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift]
  simp only [Category.id_comp, Category.comp_id]
  change _ = _ ≫ (DerivedCategory.homologyFunctor E n).map
    (DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).hom.app K))
  rw [Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  repeat erw [(DerivedCategory.homologyFunctor _ n).map_id]
  simp only [Category.comp_id]
  exact h

private lemma plus_homology_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (n : ℤ) (K : DerivedCategory.Plus C) :
    e.hom.app ((DerivedCategory.Plus.homologyFunctor C n).obj K) ≫
        (G.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (F.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.Plus.homologyFunctor D n).map
          ((Functor.mapDerivedCategoryPlusNatIso e).hom.app K) := by
  have h := Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality e n
    (DerivedCategory.Plus.ι.obj K)
  dsimp [Functor.mapDerivedCategoryPlusHomologyFunctorIso,
    Functor.mapDerivedCategoryPlusCompatibility, DerivedCategory.Plus.homologyFunctor,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift]
  simp only [Category.id_comp, Category.comp_id]
  change _ = _ ≫ (DerivedCategory.homologyFunctor D n).map
    (DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusNatIso e).hom.app K))
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  repeat erw [(DerivedCategory.homologyFunctor _ n).map_id]
  simp only [Category.comp_id]
  exact h

private lemma local_mapDerivedCategoryPlusNatIso_hom_app_singleFunctor {F G : C ⥤ D} [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryPlusNatIso e).hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
      (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
        (DerivedCategory.Plus.singleFunctor D 0).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact mapDerivedCategoryNatIso_hom_app_singleFunctor e X

private lemma local_mapDerivedCategoryPlusCompIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (mapDerivedCategoryPlusCompIso F G).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategoryPlus.map ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategoryPlusSingleFunctor 0).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  have hmap : ∀ {X Y : DerivedCategory.Plus D} (f : X ⟶ Y),
      DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map f) =
        G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := fun _ => rfl
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, hmap]
  exact mapDerivedCategoryCompIso_hom_app_singleFunctor F G X


private lemma local_mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor {F₁₂ : C ⥤ E}
    (F₂ : C ⥤ D) (F₁ : D ⥤ E) [F₁₂.Additive] [F₂.Additive] [F₁.Additive]
    [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁] (e : F₁₂ ≅ F₂ ⋙ F₁) (X : C) :
    (mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso F₂ F₁).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      F₁.mapDerivedCategoryPlus.map ((F₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (F₁.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F₂.obj X) =
    (F₁₂.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor E 0).map (e.hom.app X) := by
  rw [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    local_mapDerivedCategoryPlusCompIso_hom_app_singleFunctor]
  exact local_mapDerivedCategoryPlusNatIso_hom_app_singleFunctor e X

end Comparisons

universe u

namespace AlgebraicGeometry.Etale
private lemma upper_comp_homology {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh).hom.app
        ((DerivedCategory.Plus.homologyFunctor _ n).obj K) ≫
      ((h₁)^*[AddCommGrpCat.{u + 1}]).map
        ((((h₂)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
      (((h₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        (((h₂)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K) =
    (((h₁₂)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh).hom.app K) := by
  rw [Comparisons.plus_homology_comp, ← Category.assoc,
    Comparisons.plus_homology_naturality]
  simp only [upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]

private lemma square_homology {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sq).inv.app
        ((DerivedCategory.Plus.homologyFunctor _ n).obj K) ≫
      ((f')^*[AddCommGrpCat.{u + 1}]).map
        ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
      (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K) =
    ((g')^*[AddCommGrpCat.{u + 1}]).map
        ((((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K) ≫
      (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K) ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g' f).inv.app K ≫
          (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} f' g (g' ≫ f) sq.w).hom.app K) := by
  have h₁ := upper_comp_homology g' f (g' ≫ f) rfl n K
  have h₂ := upper_comp_homology f' g (g' ≫ f) sq.w n K
  simp only [squareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [h₂]
  apply (cancel_epi ((upperStarComp AddCommGrpCat.{u + 1} g' f).hom.app
    ((DerivedCategory.Plus.homologyFunctor _ n).obj K))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]

private lemma upper_comp_single {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂)
    (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      ((h₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
        ((((h₂)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      (((h₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((h₂)^*[AddCommGrpCat.{u + 1}]).obj F) =
    (((h₁₂)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh).hom.app F) := by
  exact Comparisons.local_mapDerivedCategoryPlusNatIso_trans_compIso_hom_app_singleFunctor
    ((h₂)^*[AddCommGrpCat.{u + 1}]) ((h₁)^*[AddCommGrpCat.{u + 1}])
    (upperStarComp AddCommGrpCat.{u + 1} h₁ h₂ h₁₂ hh) F

private lemma square_single {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g' f).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} f' g (g' ≫ f) sq.w).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      ((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
        ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((g)^*[AddCommGrpCat.{u + 1}]).obj F) =
    ((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
        ((((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((f)^*[AddCommGrpCat.{u + 1}]).obj F) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sq).inv.app F) := by
  have h₁ := upper_comp_single g' f (g' ≫ f) rfl F
  have h₂ := upper_comp_single f' g (g' ≫ f) sq.w F
  rw [h₂]
  apply (cancel_epi ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g' f).hom.app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h₁]
  simp only [squareUpperStarIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
end AlgebraicGeometry.Etale


open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

private lemma upper_comp_transport {R S T : Scheme.{u}} (v : T ⟶ S) (w : S ⟶ R)
    (c c' : T ⟶ R) (e : c = c') (hc : c = v ≫ w) (hc' : c' = v ≫ w)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    eqToHom (congrArg (fun t ↦ ((t)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K) e) ≫
        (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} v w c' hc').hom.app K =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} v w c hc).hom.app K := by
  subst c'
  simp

section CubePasting
open scoped CategoryTheory.Functor
variable {S T X X' S₀ T₀ X₀ X₁ : Scheme.{u}}
  {g : T ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ T}
  {jA : S₀ ⟶ S} {jB : T₀ ⟶ T} {g₀ : T₀ ⟶ S₀}
  {p₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ S₀} {p₁ : X₁ ⟶ X₀} {f₁ : X₁ ⟶ T₀}
  {b : X₁ ⟶ X'}

private theorem derivedExchange_transport
    {S T X Y : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T}
    {a a' : T ⟶ S} {b b' : Y ⟶ X}
    (sq : CommSq b f' f a) (sq' : CommSq b' f' f a')
    (ha : a = a') (hb : b = b')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K)) ha) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq').app K =
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K ≫
      (R+((f')_*[AddCommGrpCat.{u + 1}])).map
        (eqToHom (congrArg (fun c ↦ (D+((c)^*[AddCommGrpCat.{u + 1}])).obj K) hb)) := by
  subst a' b'
  simp

/-- The two factorizations of the outer derived mate agree after the
inverse-image composition identifications of the commuting cube.

Proof: form the horizontal composite of `sq` and `sqB`, and the horizontal
composite of `sq₀` and `sq₁`. Apply `derivedBaseChangeMapPlus_paste_horiz` to
each composite at `K`. The outer horizontal maps are identified by `h` and
`hb`, so transport one outer square along these equalities; its commutativity
proof agrees with the other by proof irrelevance. Naturality of the
inverse-image composition isomorphisms transports the resulting mate.
Precompose by the inverse of the composition isomorphism for `jB,g`, and
postcompose by the direct-image of the composition isomorphism for `p₁,p₀`.
Cancel each adjacent hom/inv pair using the isomorphism identities and
functoriality. The displayed equality is the remaining composite. This
argument concerns arbitrary complexes and commuting squares, so it needs
no properness, cartesianness, degree, or stalk assumptions; it also applies
to zero complexes and identity cubes.

Source: Stacks Project, Tags 03Q9 and 095T; the first proof step of
`lem-weil-pbc-abelian-exchange-cube-comparisons`, before single-complex naturality.
(blueprint: lem-weil-pbc-abelian-exchange-cube-comparisons). -/
private theorem derivedExchangeCube_pasting
    (sq : CommSq g' f' f g) (sq₀ : CommSq p₀ f₀ f jA)
    (sq₁ : CommSq p₁ f₁ f₀ g₀) (sqB : CommSq b f₁ f' jB)
    (h : jB ≫ g = g₀ ≫ jA) (hb : b ≫ g' = p₁ ≫ p₀)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (D+((jB)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB).app
        ((D+((g')^*[AddCommGrpCat.{u + 1}])).obj K) ≫
      (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b g').inv.app K ≫
          eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K) hb) ≫
          (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app K) =
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app _ ≫
      eqToHom (congrArg (fun a ↦ (D+((a)^*[AddCommGrpCat.{u + 1}])).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K)) h) ≫
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g₀ jA).hom.app _ ≫
      (D+((g₀)^*[AddCommGrpCat.{u + 1}])).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₀).app K) ≫
      (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app
        ((D+((p₀)^*[AddCommGrpCat.{u + 1}])).obj K) := by
  let outerA : CommSq (b ≫ g') f₁ f (jB ≫ g) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, sqB.w, Category.assoc]⟩
  let outerB : CommSq (p₁ ≫ p₀) f₁ f (g₀ ≫ jA) := ⟨by
    rw [Category.assoc, sq₀.w, ← Category.assoc, sq₁.w, Category.assoc]⟩
  have hpA := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq sqB outerA) K
  have hpB := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₀ sq₁ outerB) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hpA hpB
  have ht := derivedExchange_transport outerA outerB h hb K
  rw [hpA, hpB] at ht
  have hw := congrArg (fun m ↦
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} jB g).inv.app
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj K) ≫ m ≫
      (R+((f₁)_*[AddCommGrpCat.{u + 1}])).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} p₁ p₀).hom.app K)) ht
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at hw
  erw [(R+((f₁)_*[AddCommGrpCat.{u + 1}])).map_id] at hw
  simpa only [Category.comp_id] using hw.symm


end CubePasting

/-- Degreewise exchange for abelian sheaves on any commutative scheme square.
This is the cohomology of the canonical bounded below derived mate, conjugated by
exact-inverse-image cohomology and inverse-image/single-complex comparisons.
No cartesian or invertibility hypothesis is used. This is the map called `P^q`, `Q^q`,
or, on a cartesian face, `β` in the node; the resolution interpretation of the latter
is `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`.
Source: Stacks Project, Tags 0EYM and 0EZT
(blueprint: lem-kun-higher-exchange-coefficient-cube). -/
noncomputable def abelianHigherExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((g)^*[AddCommGrpCat.{u + 1}]).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((g')^*[AddCommGrpCat.{u + 1}]).obj F))) :=
  (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The higher exchange square commutes for an arbitrary coefficient morphism.
The initial inverse of `squareUpperStarIso sqf` identifies `x⁻¹ f₀⁻¹` with `f₁⁻¹ s⁻¹`.
The final inverse of `squareUpperStarIso sqe` is `χ : y⁻¹ e₀⁻¹ ≅ e₁⁻¹ a⁻¹`.
Functor composition with `singleFunctor`, derived direct image, and `homologyFunctor`
is exactly `R^q` on coefficient morphisms. Thus the left path is `β₁ ∘ Uφ`, and the
right path is `Vφ ∘ x⁻¹β₀`.

Proof (the four steps of the node):
1. Put `K₀ = F₀[0]`, `K₁ = F₁[0]`. The single-complex comparison turns `φ` into
   `a⁻¹K₀ ⟶ K₁`. Apply lem-kun-derived-exchange-cube to the six commuting faces
   and `K₀`, inserting the canonical inverse-image composition comparisons.
2. Use naturality of def-kun-commutative-derived-exchange at this coefficient map.
   Precompose with the comparison-face exchange and substitute the derived cube
   identity from step 1. Associativity gives the desired derived equality.
3. Apply lem-weil-pbc-exact-functor-complex-cohomology to inverse images. Descend
   its natural comparisons through lem-weil-pbc-localization-universal-property,
   clauses (2) and (3). The termwise description in
   lem-weil-pbc-derived-inverse-image-composition identifies their composition
   comparisons with the ordinary sheaf comparisons, including `χ`.
4. Apply degree-`q` cohomology. def-weil-pbc-direct-image identifies the resulting
   functors and their maps with `R^q`. On the two cartesian faces, the canonical
   commutative-square comparison and def-weil-pbc-derived-square-iso have the same
   termwise composite and hence the same derived class by localization. Their mates
   agree with def-weil-pbc-derived-exchange. Consequently lem-kun-bc-map-on-cohomology
   identifies the two remaining factors with the usual higher base-change maps.
   The other factors are precisely the displayed coefficient maps and `χ`.
Neither the coefficient map nor the comparison exchanges are inverted.
Source: Stacks Project, Tags 0EYM and 0EZT
(blueprint: lem-kun-higher-exchange-coefficient-cube). -/
theorem abelianHigherExchange_coefficient_cube
    {X₀ Y₀ S₀ T₀ X₁ Y₁ S₁ T₁ : Scheme.{u}}
    {h₀ : Y₀ ⟶ X₀} {e₀ : Y₀ ⟶ T₀} {f₀ : X₀ ⟶ S₀} {g₀ : T₀ ⟶ S₀}
    {h₁ : Y₁ ⟶ X₁} {e₁ : Y₁ ⟶ T₁} {f₁ : X₁ ⟶ S₁} {g₁ : T₁ ⟶ S₁}
    {x : X₁ ⟶ X₀} {y : Y₁ ⟶ Y₀} {s : S₁ ⟶ S₀} {a : T₁ ⟶ T₀}
    (sq₀ : ChosenCartesianSquare e₀ h₀ g₀ f₀)
    (sq₁ : ChosenCartesianSquare e₁ h₁ g₁ f₁)
    (sqf : CommSq x f₁ f₀ s) (sqg : CommSq a g₁ g₀ s)
    (sqh : CommSq y h₁ h₀ x) (sqe : CommSq y e₁ e₀ a)
    (F₀ : Sheaf T₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf T₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁) (q : ℕ) :
    (squareUpperStarIso AddCommGrpCat.{u + 1} sqf).inv.app
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F₀))) ≫
    ((f₁)^*[AddCommGrpCat.{u + 1}]).map
      (abelianHigherExchange sqg F₀ q ≫
        (DerivedCategory.Plus.singleFunctor _ 0 ⋙
          (g₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map φ) ≫
    abelianHigherExchange sq₁.toCommSq F₁ q =
    ((x)^*[AddCommGrpCat.{u + 1}]).map (abelianHigherExchange sq₀.toCommSq F₀ q) ≫
    abelianHigherExchange sqh (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀) q ≫
    (DerivedCategory.Plus.singleFunctor _ 0 ⋙
      (h₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((squareUpperStarIso AddCommGrpCat.{u + 1} sqe).inv.app F₀ ≫
        ((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) := by
  let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj F₀
  let u := (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map φ
  have hd := (derivedExchangeCube_pasting sq₀.toCommSq sqg sq₁.toCommSq sqh
    sqf.w sqe.w K₀).symm
  have hfcomp := upper_comp_transport f₁ s (x ≫ f₀) (f₁ ≫ s) sqf.w sqf.w rfl
    ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K₀)
  have hecomp := upper_comp_transport e₁ a (y ≫ e₀) (e₁ ≫ a) sqe.w sqe.w rfl K₀
  rw [reassoc_of% hfcomp, hecomp] at hd
  have hn := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁.toCommSq).naturality u
  dsimp only [Functor.comp_map] at hn
  have he := congrArg (fun t ↦ t ≫
    (h₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      (((e₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map u ≫
        (((e₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₁)) hd
  simp only [Functor.map_comp, Category.assoc] at he
  rw [← reassoc_of% hn] at he
  have hc :=
    (((e₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality φ
  dsimp only [Functor.comp_map] at hc
  have ht :
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} y e₀).inv.app K₀ ≫
        (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} e₁ a (y ≫ e₀) sqe.w).hom.app K₀ ≫
        ((e₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map u ≫
        (((e₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₁ =
      ((y)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
          ((((e₀)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀) ≫
        (((y)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          (((e₀)^*[AddCommGrpCat.{u + 1}]).obj F₀) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((squareUpperStarIso AddCommGrpCat.{u + 1} sqe).inv.app F₀) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (((e₁)^*[AddCommGrpCat.{u + 1}]).map φ) := by
    dsimp only [u, K₀]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    exact (reassoc_of% square_single sqe F₀) _
  have htr := congrArg (h₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map ht
  simp only [Functor.map_comp] at htr
  rw [htr] at he
  have hq := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqh).naturality
    ((((e₀)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀)
  dsimp only [Functor.comp_map] at hq
  rw [← reassoc_of% hq] at he
  have hw := congrArg (fun t ↦
    ((x)^*[AddCommGrpCat.{u + 1}]).map
        ((((f₀)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
          (q : ℤ)).hom.app ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K₀)) ≫
      (((x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).hom.app
          (((f₀)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj
            ((g₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K₀)) ≫
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map t) he
  simp only [Functor.map_comp] at hw
  simp only [abelianHigherExchange, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (((f₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.naturality]
  rw [reassoc_of% (((f₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.naturality]
  rw [reassoc_of% (((f₁)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.naturality]
  rw [reassoc_of% square_homology sqf (q : ℤ)]
  rw [reassoc_of% (((x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.naturality]
  rw [reassoc_of% (((x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.naturality]
  dsimp only [u] at hw
  simp only [Functor.map_comp] at hw ⊢
  exact hw

end AlgebraicGeometry.Etale
