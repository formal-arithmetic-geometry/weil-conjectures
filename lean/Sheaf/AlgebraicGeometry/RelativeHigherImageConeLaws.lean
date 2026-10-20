/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.AlgebraicGeometry.RelativeHigherImageContinuityPreorder

import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.CategoryTheory.Localization.Predicate


/-!
# The diagram and cone laws for relative higher images

Source: Stacks Project, Tag 0EYM, first proof paragraph
(blueprint: lem-kun-relative-higher-image-cone-laws).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory

/-- The laws for specified objects, transition maps and cocone legs. -/
structure DiagramCoconeLaws {J C : Type*} [Category J] [Category C]
    (O : J → C) (M : ∀ {i j : J}, (i ⟶ j) → (O i ⟶ O j))
    (P : C) (L : ∀ i : J, O i ⟶ P) : Prop where
  map_id : ∀ i, M (𝟙 i) = 𝟙 (O i)
  map_comp : ∀ (i j k : J) (a : i ⟶ j) (b : j ⟶ k), M (a ≫ b) = M a ≫ M b
  leg : ∀ (i j : J) (a : i ⟶ j), M a ≫ L j = L i

/-- A diagram presented by specified objects and maps, together with specified cocone legs. -/
structure PresentedDiagramWithLegs {J C : Type*} [Category J] [Category C]
    (O : J → C) (M : ∀ {i j : J}, (i ⟶ j) → (O i ⟶ O j))
    (P : C) (L : ∀ i : J, O i ⟶ P) where
  diagram : J ⥤ C
  objIso : ∀ i, diagram.obj i ≅ O i
  transition : ∀ (i j : J) (a : i ⟶ j),
    diagram.map a = (objIso i).hom ≫ M a ≫ (objIso j).inv
  legs : diagram ⟶ (Functor.const J).obj P
  leg_eq : ∀ i, legs.app i = (objIso i).hom ≫ L i

/-- Construct the presented diagram from the explicit data and their laws. The
implementation is irreducible so users work through the presentation's equations. -/
@[irreducible]
def presentedDiagramWithLegsOfLaws {J C : Type*} [Category J] [Category C]
    (O : J → C) (M : ∀ {i j : J}, (i ⟶ j) → (O i ⟶ O j))
    (P : C) (L : ∀ i : J, O i ⟶ P) (h : DiagramCoconeLaws O M P L) :
    PresentedDiagramWithLegs O M P L where
  diagram :=
    { obj := O
      map := M
      map_id := h.map_id
      map_comp := fun {i j k} a b ↦ h.map_comp i j k a b }
  objIso := fun i ↦ Iso.refl (O i)
  transition := by
    intro i j a
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  legs :=
    { app := L
      naturality := by
        intro i j a
        exact (h.leg i j a).trans (Category.comp_id (L i)).symm }
  leg_eq := by intro i; exact (Category.id_comp (L i)).symm

end CategoryTheory

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




/-- The degree-`q` higher direct image functor on abelian sheaves. -/
noncomputable abbrev higherImageFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)

/-- The stage higher image pulled to the limiting base. -/
noncomputable abbrev relativeHigherImageObj
    {I : Type u} [Preorder I] (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    (cB : Cone DB)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) : Sheaf cB.pt.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((cB.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj
    ((higherImageFunctor (η.app (op i)) q).obj (F i))

/-- The canonical transition on pulled-back stage higher images. -/
noncomputable def relativeHigherImageMap
    {I : Type u} [Preorder I] (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    (cB : Cone DB)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      ((DV.map a.op)^*[AddCommGrpCat.{u + 1}]).obj (F i) ⟶ F j)
    (q : ℕ) {i j : I} (a : i ⟶ j) :
    relativeHigherImageObj DV DB η cB F q i ⟶ relativeHigherImageObj DV DB η cB F q j :=
  (upperStarComp AddCommGrpCat.{u + 1} (cB.π.app (op j)) (DB.map a.op)
    (cB.π.app (op i)) (cB.w a.op).symm).hom.app
      ((higherImageFunctor (η.app (op i)) q).obj (F i)) ≫
    ((cB.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map
      (relativeHigherImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q)

/-- The canonical comparison leg into the limit higher image. -/
noncomputable def relativeHigherImageLeg
    {I : Type u} [Preorder I] (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    (cV : Cone DV) (cB : Cone DB) (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i, A.obj i ≅ ((cV.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj (F i))
    (cA : Cocone A) (q : ℕ) (i : I) :
    relativeHigherImageObj DV DB η cB F q i ⟶ (higherImageFunctor v q).obj cA.pt :=
  relativeHigherImageExchange ⟨hu (op i)⟩ (F i) cA.pt
    ((eA i).inv ≫ cA.ι.app i) q

private lemma transfer_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (H₀ : C₀ ⥤ D₀) (H₁ : C₁ ⥤ D₁) (H₂ : C₂ ⥤ D₂)
    (U₀₁ : C₀ ⥤ C₁) (U₁₂ : C₁ ⥤ C₂) (U₀₂ : C₀ ⥤ C₂)
    (V₀₁ : D₀ ⥤ D₁) (V₁₂ : D₁ ⥤ D₂) (V₀₂ : D₀ ⥤ D₂)
    (α₀₁ : H₀ ⋙ V₀₁ ⟶ U₀₁ ⋙ H₁) (α₁₂ : H₁ ⋙ V₁₂ ⟶ U₁₂ ⋙ H₂)
    (α₀₂ : H₀ ⋙ V₀₂ ⟶ U₀₂ ⋙ H₂)
    (c : V₀₂ ⟶ V₀₁ ⋙ V₁₂) (d : U₀₂ ⟶ U₀₁ ⋙ U₁₂)
    (hc : ∀ X, c.app (H₀.obj X) ≫ V₁₂.map (α₀₁.app X) ≫
      α₁₂.app (U₀₁.obj X) = α₀₂.app X ≫ H₂.map (d.app X))
    {X : C₀} {Y : C₁} {Z : C₂}
    (a : U₀₁.obj X ⟶ Y) (b : U₁₂.obj Y ⟶ Z) (e : U₀₂.obj X ⟶ Z)
    (he : e = d.app X ≫ U₁₂.map a ≫ b) :
    α₀₂.app X ≫ H₂.map e =
      c.app (H₀.obj X) ≫ V₁₂.map (α₀₁.app X ≫ H₁.map a) ≫
        α₁₂.app Y ≫ H₂.map b := by
  have ht := α₁₂.naturality a
  dsimp only [Functor.comp_map] at ht
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht, reassoc_of% hc X]

private lemma relative_exchange_formula
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((g')^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') (q : ℕ) :
    relativeHigherImageExchange sq F F' φ q =
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
              (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
                ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor
                  0).hom.app F ≫ (DerivedCategory.Plus.singleFunctor _ 0).map φ)) := by
  rfl

private lemma relative_exchange_comp
    {V₀ B₀ V₁ B₁ V₂ B₂ : Scheme.{u}}
    {v₀ : V₀ ⟶ B₀} {v₁ : V₁ ⟶ B₁} {v₂ : V₂ ⟶ B₂}
    {a : V₁ ⟶ V₀} {b : V₂ ⟶ V₁} {c : V₂ ⟶ V₀}
    {x : B₁ ⟶ B₀} {y : B₂ ⟶ B₁} {z : B₂ ⟶ B₀}
    (sq₁ : CommSq a v₁ v₀ x) (sq₂ : CommSq b v₂ v₁ y)
    (sq : CommSq c v₂ v₀ z) (hc : c = b ≫ a) (hz : z = y ≫ x)
    (F₀ : Sheaf V₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₁ : Sheaf V₁.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F₂ : Sheaf V₂.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F₀ ⟶ F₁)
    (ψ : ((b)^*[AddCommGrpCat.{u + 1}]).obj F₁ ⟶ F₂) (q : ℕ) :
    relativeHigherImageExchange sq F₀ F₂
      ((upperStarComp AddCommGrpCat.{u + 1} b a c hc).hom.app F₀ ≫
        ((b)^*[AddCommGrpCat.{u + 1}]).map φ ≫ ψ) q =
    (upperStarComp AddCommGrpCat.{u + 1} y x z hz).hom.app
        ((higherImageFunctor v₀ q).obj F₀) ≫
      ((y)^*[AddCommGrpCat.{u + 1}]).map
        (relativeHigherImageExchange sq₁ F₀ F₁ φ q) ≫
      relativeHigherImageExchange sq₂ F₁ F₂ ψ q := by
  simp only [relative_exchange_formula]
  subst hc
  subst hz
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F₀
  let u := (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let w := (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₁ ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map ψ
  have hs : (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).inv.app K ≫
        (((b ≫ a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} b a).hom.app F₀ ≫
            ((b)^*[AddCommGrpCat.{u + 1}]).map φ ≫ ψ) =
      ((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map u ≫ w := by
    have hc := congrArg (fun z ↦
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a).inv.app K ≫ z)
        (upper_comp_single b a (b ≫ a) rfl F₀)
    dsimp only [K] at hc
    simp only [Iso.inv_hom_id_app_assoc] at hc
    simp only [u, w, Functor.map_comp, Category.assoc]
    have hn :=
      (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality φ
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, reassoc_of% hc]
  have hd := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp] at hd
  have he := congrArg (fun z ↦ z ≫
    (v₂)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      ((((b ≫ a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} b a).hom.app F₀ ≫
            ((b)^*[AddCommGrpCat.{u + 1}]).map φ ≫ ψ))) hd
  simp only [Category.assoc, ← Functor.map_comp] at he
  rw [hs] at he
  simp only [Functor.map_comp] at he
  have hn := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).naturality u
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn] at he
  let t :=
    (((b ≫ a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F₀ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a).hom.app F₀ ≫
          ((b)^*[AddCommGrpCat.{u + 1}]).map φ ≫ ψ)
  exact transfer_composition
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ))
    ((x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus
    ((y)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus
    ((y ≫ x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus
    ((x)^*[AddCommGrpCat.{u + 1}]) ((y)^*[AddCommGrpCat.{u + 1}])
    ((y ≫ x)^*[AddCommGrpCat.{u + 1}])
    (((x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom
    (((y)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom
    (((y ≫ x)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
      (q : ℤ)).hom
    (upperStarComp AddCommGrpCat.{u + 1} y x).hom
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} y x).hom
    (upper_comp_homology y x (y ≫ x) rfl (q : ℤ))
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K ≫
      (v₁)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map u)
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F₁) ≫
        (v₂)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map w)
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K ≫
      (v₂)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map t)
    (by simpa only [t, Functor.map_comp, Category.assoc] using he)

private lemma upper_comp_associativity
    {B₀ B₁ B₂ B₃ : Scheme.{u}}
    (a : B₁ ⟶ B₀) (b : B₂ ⟶ B₁) (r : B₃ ⟶ B₂)
    (c : B₂ ⟶ B₀) (s : B₃ ⟶ B₁) (p : B₃ ⟶ B₀)
    (hc : c = b ≫ a) (hs : s = r ≫ b) (hp : p = s ≫ a)
    (F : Sheaf B₀.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} r c p
      (by rw [hc, hp, hs, Category.assoc])).hom.app F ≫
      ((r)^*[AddCommGrpCat.{u + 1}]).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a c hc).hom.app F) =
    (upperStarComp AddCommGrpCat.{u + 1} s a p hp).hom.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} r b s hs).hom.app
        (((a)^*[AddCommGrpCat.{u + 1}]).obj F) := by
  subst hc
  subst hs
  subst hp
  have h := congrArg (fun t ↦ t.hom.app F)
    (upperStarComp_assoc AddCommGrpCat.{u + 1} r b a ((r ≫ b) ≫ a)
      (Category.assoc r b a))
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] using h

private lemma relative_exchange_iso_of_id
    {V B : Scheme.{u}} (v : V ⟶ B) (a : V ⟶ V) (x : B ⟶ B)
    (ha : a = 𝟙 V) (hx : x = 𝟙 B) (sq : CommSq a v v x)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F) [IsIso φ] (q : ℕ) :
    IsIso (relativeHigherImageExchange sq F F φ q) := by
  subst ha
  subst hx
  have : IsIso (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq) := by
    rw [derivedBaseChangeMapPlus_id]
    infer_instance
  rw [relative_exchange_formula]
  infer_instance


/-- The canonical higher-image transitions form a diagram, and the canonical
projection exchanges followed by the coefficient cocone form a cocone.

Source: Stacks Project, Tag 0EYM, first proof paragraph
(blueprint: lem-kun-relative-higher-image-cone-laws).

Proof: Horizontally paste the commutative transition squares. The composition
comparison for inverse image along their composite equals the composite of the
comparisons, by inverse-image associativity. Horizontal pasting for derived
exchange and naturality in the coefficients then identify the transition for a
composite with the composite of transitions. The identity pasting law gives the
identity transition. For the leg equation, paste a transition square with the
projection square at its target. Naturality moves the coefficient transition
through exchange. The coefficient cocone equation identifies the resulting
coefficient map with the projection leg at the source. Apply degree-q cohomology;
exact inverse image commutes with cohomology, and its comparison is compatible
with identity and composition. This proves all three displayed equations. No
cartesian, affine, quasi-compact, torsion or limit hypothesis is needed. -/
theorem relativeHigherImage_cone_laws
    {I : Type u} [Preorder I]
    (DV DB : Iᵒᵖ ⥤ Scheme.{u}) (η : DV ⟶ DB)
    (cV : Cone DV) (cB : Cone DB) (v : cV.pt ⟶ cB.pt)
    (hu : ∀ i, cV.π.app i ≫ η.app i = v ≫ cB.π.app i)
    (F : ∀ i : I, Sheaf (DV.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (a : i ⟶ j),
      ((DV.map a.op)^*[AddCommGrpCat.{u + 1}]).obj (F i) ⟶ F j)
    (hid : ∀ i, φ (𝟙 i) =
      eqToHom (congrArg (fun a : DV.obj (op i) ⟶ DV.obj (op i) ↦
        ((a)^*[AddCommGrpCat.{u + 1}]).obj (F i)) (DV.map_id (op i))) ≫
        (upperStarId AddCommGrpCat.{u + 1} (DV.obj (op i))).hom.app (F i))
    (hcomp : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k), φ (a ≫ b) =
      (upperStarComp AddCommGrpCat.{u + 1} (DV.map b.op) (DV.map a.op)
        (DV.map (a ≫ b).op) (DV.map_comp b.op a.op)).hom.app (F i) ≫
      ((DV.map b.op)^*[AddCommGrpCat.{u + 1}]).map (φ a) ≫ φ b)
    (A : I ⥤ Sheaf cV.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eA : ∀ i, A.obj i ≅ ((cV.π.app (op i))^*[AddCommGrpCat.{u + 1}]).obj (F i))
    (hA : ∀ (i j : I) (a : i ⟶ j), A.map a ≫ (eA j).hom =
      (eA i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
        ((cV.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (φ a))
    (cA : Cocone A) (q : ℕ) :
    DiagramCoconeLaws (relativeHigherImageObj DV DB η cB F q)
      (relativeHigherImageMap DV DB η cB F φ q) ((higherImageFunctor v q).obj cA.pt)
      (relativeHigherImageLeg DV DB η cV cB v hu F A eA cA q) := by
  have hm : ∀ (i j k : I) (a : i ⟶ j) (b : j ⟶ k),
      relativeHigherImageMap DV DB η cB F φ q (a ≫ b) =
        relativeHigherImageMap DV DB η cB F φ q a ≫
          relativeHigherImageMap DV DB η cB F φ q b := by
    intro i j k a b
    dsimp only [relativeHigherImageMap]
    rw [hcomp i j k a b]
    rw [relative_exchange_comp ⟨η.naturality a.op⟩ ⟨η.naturality b.op⟩
      ⟨η.naturality (a ≫ b).op⟩ (DV.map_comp b.op a.op) (DB.map_comp b.op a.op)
      (F i) (F j) (F k) (φ a) (φ b) q]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% upper_comp_associativity (DB.map a.op) (DB.map b.op)
      (cB.π.app (op k)) (DB.map (a ≫ b).op) (cB.π.app (op j)) (cB.π.app (op i))
      (DB.map_comp b.op a.op) (cB.w b.op).symm (cB.w a.op).symm]
    have hn := (upperStarComp AddCommGrpCat.{u + 1}
      (cB.π.app (op k)) (DB.map b.op) (cB.π.app (op j)) (cB.w b.op).symm).hom.naturality
        (relativeHigherImageExchange ⟨η.naturality a.op⟩ (F i) (F j) (φ a) q)
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    rfl
  refine ⟨?_, hm, ?_⟩
  · intro i
    have : IsIso (φ (𝟙 i)) := by rw [hid i]; infer_instance
    have := relative_exchange_iso_of_id (η.app (op i))
      (DV.map (𝟙 i).op) (DB.map (𝟙 i).op) (DV.map_id (op i)) (DB.map_id (op i))
      ⟨η.naturality (𝟙 i).op⟩ (F i) (φ (𝟙 i)) q
    have : IsIso (relativeHigherImageMap DV DB η cB F φ q (𝟙 i)) := by
      dsimp only [relativeHigherImageMap]
      infer_instance
    apply (cancel_epi (relativeHigherImageMap DV DB η cB F φ q (𝟙 i))).1
    simpa only [Category.id_comp, Category.comp_id] using
      (hm i i i (𝟙 i) (𝟙 i)).symm
  · intro i j a
    have hc :
        (upperStarComp AddCommGrpCat.{u + 1} (cV.π.app (op j)) (DV.map a.op)
          (cV.π.app (op i)) (cV.w a.op).symm).hom.app (F i) ≫
          ((cV.π.app (op j))^*[AddCommGrpCat.{u + 1}]).map (φ a) ≫
            ((eA j).inv ≫ cA.ι.app j) = (eA i).inv ≫ cA.ι.app i := by
      have hd := congrArg (fun z ↦ (eA i).inv ≫ z ≫ (eA j).inv ≫ cA.ι.app j)
        (hA i j a)
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] at hd
      rw [cA.w a] at hd
      exact hd.symm
    have hl := relative_exchange_comp ⟨η.naturality a.op⟩ ⟨hu (op j)⟩ ⟨hu (op i)⟩
      (cV.w a.op).symm (cB.w a.op).symm (F i) (F j) cA.pt
      (φ a) ((eA j).inv ≫ cA.ι.app j) q
    rw [hc] at hl
    exact hl.symm


end AlgebraicGeometry.Etale
