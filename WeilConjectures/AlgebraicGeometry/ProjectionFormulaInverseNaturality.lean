/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral

/-!
# Naturality of the specified projection inverse

Source: Weil conjectures blueprint, proper base change, definition 1264 and lemma 1266
(blueprint: lem-weil-pbc-projection-inverse-coefficient-naturality).
-/

@[expose] public section

universe u v u' v' w w'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory
variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) (V : B ⥤ A) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
  (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom = (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
private theorem beta_naturality (K F G : CochainComplex A ℤ) (f : F ⟶ G) :
    tensorPullbackTotal L e he K F ≫
      (L.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K) f (curriedTensor A) (.up ℤ)) =
    HomologicalComplex.mapBifunctorMap
      (𝟙 ((L.mapHomologicalComplex (.up ℤ)).obj K))
      ((L.mapHomologicalComplex (.up ℤ)).map f) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he K G := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (e X Y).inv ≫ L.map (a ⊗ₘ b) =
        (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv := by
    apply (cancel_mono (e X' Y').hom).1
    rw [Category.assoc, he, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    tensorPullbackTotalComponent, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    Functor.mapHomologicalComplex_map_f]
  rw [← L.map_comp, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.map_comp, HomologicalComplex.id_f, curriedTensor_obj_map, Functor.map_id]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, NatTrans.id_app,
    Category.id_comp, curriedTensor_obj_map, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.ι_mapBifunctorDesc, Functor.map_id]
  change (e (K.X a) (F.X b)).inv ≫ L.map (𝟙 (K.X a ⊗ F.X b)) ≫
      L.map (K.X a ◁ f.f b) ≫ L.map (K.ιMapBifunctor G (curriedTensor A) a b n hab) =
    (L.obj (K.X a) ◁ L.map (f.f b)) ≫ (e (K.X a) (G.X b)).inv ≫
      L.map (K.ιMapBifunctor G (curriedTensor A) a b n hab)
  simp only [Functor.map_id, Category.id_comp]
  simpa only [Functor.map_id, Category.id_comp, tensorHom_id, id_tensorHom,
      Category.assoc, Functor.mapHomologicalComplex_obj_X] using
    congrArg (fun z ↦ z ≫ L.map
      (CochainComplex.ιMapBifunctor K G (curriedTensor A) a b n hab))
      (hi (𝟙 (K.X a)) (f.f b))
private theorem inverse_square
    {Z : Type*} [Category Z] {X Y X' Y' : Z} (s : X ⟶ Y) (t : X' ⟶ Y') [IsIso s] [IsIso t]
    (a : X ⟶ X') (b : Y ⟶ Y') (h : s ≫ b = a ≫ t) :
    b ≫ inv t = inv s ≫ a := by
  apply (cancel_epi s).1
  rw [← Category.assoc s b, h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem total_naturality (K : CochainComplex B ℤ)
    (F G : CochainComplex A ℤ) (f : F ⟶ G) :
    HomologicalComplex.mapBifunctorMap
      (𝟙 ((V.mapHomologicalComplex (.up ℤ)).obj K)) f (curriedTensor A) (.up ℤ) ≫
      tensorAdjunctionTotal L V adj e he K G =
    tensorAdjunctionTotal L V adj e he K F ≫
      (V.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap (𝟙 K)
          ((L.mapHomologicalComplex (.up ℤ)).map f) (curriedTensor B) (.up ℤ)) := by
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  let a := adj.mapHomologicalComplex (.up ℤ)
  have : IsIso (tensorPullbackTotal L e he (VC.obj K) F) :=
    tensorPullbackTotal_isIso L e he V adj _ _
  have : IsIso (tensorPullbackTotal L e he (VC.obj K) G) :=
    tensorPullbackTotal_isIso L e he V adj _ _
  have hbeta := inverse_square _ _ _ _ (beta_naturality L e he (VC.obj K) F G f)
  apply (a.homEquiv _ _).symm.injective
  dsimp only [tensorAdjunctionTotal]
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [a, Equiv.symm_apply_apply]
  rw [← Category.assoc, hbeta, Category.assoc, Category.assoc]
  congr 1
  exact (((curriedTensor B).map₂CochainComplex.map (a.counit.app K)).naturality
    (LC.map f))
private theorem rectangle_naturality
    {Z : Type*} [Category Z] {P P' A A' T T' C C' : Z}
    (s : P ⟶ A) (s' : P' ⟶ A') [Epi s]
    (r : P ⟶ T) (r' : P' ⟶ T') (t : T ⟶ C) (t' : T' ⟶ C')
    (z : A ⟶ C) (z' : A' ⟶ C')
    (a : A ⟶ A') (b : C ⟶ C') (p : P ⟶ P') (q : T ⟶ T')
    (hz : s ≫ z = r ≫ t) (hz' : s' ≫ z' = r' ≫ t')
    (hs : s ≫ a = p ≫ s') (hr : p ≫ r' = r ≫ q)
    (ht : q ≫ t' = t ≫ b) : a ≫ z' = z ≫ b := by
  apply (cancel_epi s).1
  calc
    s ≫ a ≫ z' = p ≫ s' ≫ z' := by rw [← Category.assoc, hs, Category.assoc]
    _ = r ≫ t ≫ b := by rw [hz', ← Category.assoc, hr, Category.assoc, ht]
    _ = s ≫ z ≫ b := by rw [← Category.assoc, ← hz, Category.assoc]

private theorem map_prod_square
    {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    (T : X × Y ⥤ Z) {x x' : X} (a : x ⟶ x')
    {p q p' q' : Y} (f : p ⟶ q) (g : p' ⟶ q') (i : p ⟶ p') (j : q ⟶ q')
    (h : i ≫ g = f ≫ j) :
    T.map (CategoryTheory.Prod.mkHom (𝟙 x) i) ≫
        T.map (CategoryTheory.Prod.mkHom a g) =
      T.map (CategoryTheory.Prod.mkHom a f) ≫
        T.map (CategoryTheory.Prod.mkHom (𝟙 x') j) := by
  rw [← T.map_comp, ← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp, Category.comp_id, h]

private theorem transported_inverse_naturality
    {Z : Type*} [Category Z] {X Y X' Y' C D C' D' : Z}
    (e : X ≅ C) (e' : X' ≅ C') (b : Y ≅ D) (b' : Y' ≅ D')
    (t : C ⟶ D) (t' : C' ⟶ D') [IsIso t] [IsIso t']
    (a : X ⟶ X') (v : Y ⟶ Y') (c : C ⟶ C') (d : D ⟶ D')
    (he : a ≫ e'.hom = e.hom ≫ c)
    (hb : v ≫ b'.hom = b.hom ≫ d) (ht : t ≫ d = c ≫ t') :
    v ≫ (b'.hom ≫ inv t' ≫ e'.inv) = (b.hom ≫ inv t ≫ e.inv) ≫ a := by
  have hinv := inverse_square t t' c d ht
  have heinv : c ≫ e'.inv = e.inv ≫ a := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc e.hom c, ← he, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hb, Category.assoc,
    ← Category.assoc d (inv t'), hinv, Category.assoc, heinv]
  simp only [Category.assoc]

end CategoryTheory

namespace CategoryTheory
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
private theorem pullback_naturality (L : A ⥤ B) [L.Additive]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    {F G : CochainComplex A ℤ} (f : F ⟶ G) :
    LF.map (DerivedCategory.Q.map f) ≫ derivedPullbackComplexComparison L LF epsilon G =
    derivedPullbackComplexComparison L LF epsilon F ≫
      DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map f) := by
  let t : DerivedCategory.Q ⋙ LF ⟶ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv LF ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) epsilon ≫
        Functor.whiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
          Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ))
            (DerivedCategory.quotientCompQhIso B).hom
  exact t.naturality f
private theorem pushforward_naturality (V : B ⥤ A) [V.Additive]
    (RF : DerivedCategory B ⥤ DerivedCategory A)
    (eta : V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    {F G : CochainComplex B ℤ} (f : F ⟶ G) :
    DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map f) ≫
      derivedPushforwardComplexComparison V RF eta G =
    derivedPushforwardComplexComparison V RF eta F ≫ RF.map (DerivedCategory.Q.map f) := by
  let t : V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF :=
    Functor.whiskerLeft (V.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso A).inv ≫
        Functor.whiskerRight (V.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
          Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) eta ≫
            Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).hom RF
  exact t.naturality f
end CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

set_option maxHeartbeats 600000 in
-- The two tensor interfaces require repeated dependent representative conversions.
private theorem mixedRepresentative_coefficient_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ×
      DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤
      DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
      ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
        (monoidalCategory R)).map₂HomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (A F G : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hf : PR F) (hg : PR G) (f : F ⟶ G) :
    TR.map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj A))
        (DerivedCategory.Q.map f)) ≫ (mixedTensorRepresentative R PR hPR TR rR A G hg).hom =
      (mixedTensorRepresentative R PR hPR TR rR A F hf).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 A) f
          (@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
            (monoidalCategory R)) (ComplexShape.up ℤ)) := by
  let := monoidalCategory R
  obtain ⟨P, p, hp, hflat, hq, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral A
  have hpR : PR P := (hPR P).mpr ⟨hp, hflat⟩
  have : QuasiIso p := hq
  have hzF := (Classical.choose_spec
    (mixedTensorRepresentative_existsUnique R PR hPR TR rR A F hf).exists) P hpR p hq
  have hzG := (Classical.choose_spec
    (mixedTensorRepresentative_existsUnique R PR hPR TR rR A G hg).exists) P hpR p hq
  change TR.map _ ≫ (mixedTensorRepresentative R PR hPR TR rR A F hf).hom = _ at hzF
  change TR.map _ ≫ (mixedTensorRepresentative R PR hPR TR rR A G hg).hom = _ at hzG
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.map₂HomologicalComplex_obj_obj, ObjectProperty.ι_obj] at hzF hzG ⊢
  have hn := rR.inv.naturality
    (CategoryTheory.Prod.mkHom (𝟙 (⟨P, hpR⟩ : PR.FullSubcategory))
      (show (⟨F, hf⟩ : PR.FullSubcategory) ⟶ ⟨G, hg⟩ from ⟨f⟩))
  have : IsIso (DerivedCategory.Q.map p) := inferInstance
  have : IsIso (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
      (𝟙 (DerivedCategory.Q.obj F))) := by
    change IsIso (Iso.prod (asIso (DerivedCategory.Q.map p))
      (Iso.refl (DerivedCategory.Q.obj F))).hom
    infer_instance
  let T := (CategoryTheory.MonoidalCategory.curriedTensor
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).map₂CochainComplex
  have ht := (T.map p).naturality f
  dsimp only [T, Functor.map₂CochainComplex] at ht
  simp only [Functor.map₂HomologicalComplex_map_app,
    Functor.map₂HomologicalComplex_obj_map] at ht
  have hswap : TR.map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
      (𝟙 (DerivedCategory.Q.obj F))) ≫
      TR.map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj A))
        (DerivedCategory.Q.map f)) =
    TR.map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.map f)) ≫
      TR.map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
        (𝟙 (DerivedCategory.Q.obj G))) := by
    rw [← TR.map_comp, ← TR.map_comp]
    simp only [CategoryTheory.prod_comp, Category.id_comp, Category.comp_id]
  have hn' :
      TR.map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
        (DerivedCategory.Q.map f)) ≫ rR.inv.app (⟨P, hpR⟩, ⟨G, hg⟩) =
      rR.inv.app (⟨P, hpR⟩, ⟨F, hf⟩) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) f _ _) := by
    dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      Functor.map₂HomologicalComplex_obj_obj, ObjectProperty.ι_obj] at hn
    simp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.id_hom, Functor.uncurry_obj_map,
      Functor.prod_obj, ObjectProperty.ι_obj, Functor.comp_obj] at hn
    have hid := congr_app (T.map_id P) F
    dsimp only [T, Functor.map₂CochainComplex] at hid
    rw [DerivedCategory.Q.map_id, hid, NatTrans.id_app, Category.id_comp] at hn
    exact hn
  exact CategoryTheory.rectangle_naturality _ _ _ _ _ _ _ _ _ _ _ _
    hzF hzG hswap hn'
    (by simpa only [← DerivedCategory.Q.map_comp] using congrArg DerivedCategory.Q.map ht)

variable
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V)
    [V.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)))
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (hRF : ∀ G : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)),
      Function.Bijective (fun b : RF ⟶ G ↦ eta ≫ Functor.whiskerLeft DerivedCategory.Qh b))
    (computeR : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      IsIso (derivedPushforwardComplexComparison V RF eta K))
    (computeL : ∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        IsIso (derivedPullbackComplexComparison uStar LF epsilon P))
    (adjD : LF ⊣ RF)
    (canonicalAdj : ∀ K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ, K.IsKInjective →
      LF.map (derivedPushforwardComplexComparison V RF eta K) ≫
          adjD.counit.app (DerivedCategory.Q.obj K) =
        derivedPullbackComplexComparison uStar LF epsilon
          ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((am.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))) (K : CochainComplex (SheafOfModules.{u} ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S)) ℤ) (hK : K.IsKInjective)
    (repE : E ≅ DerivedCategory.Q.obj K)

set_option maxHeartbeats 800000 in
-- Keep all derived and ordinary representative isomorphisms explicit.
/-- Naturality of the specified finite-total inverse in the coefficient complex.
Source: proper base change, definition 1264 and lemma 1266, naturality of the
summand maps (blueprint: lem-weil-pbc-projection-inverse-coefficient-naturality).
Proof: naturality of the ordinary tensor comparison and of the counit gives a
commuting square for the forward chain mates. Invert these chain isomorphisms
to obtain the square for their finite-total inverses. The mixed tensor
representative squares are natural in the K-flat coefficient: precompose with
one K-flat resolution of the first factor and use naturality of rR or rS;
cancel the localized resolution. The complex comparisons for derived pullback
and pushforward are natural as composites of natural transformations. Transport
the inverse chain square through these representative isomorphisms to obtain
the displayed square. This also covers the zero complex and zero maps. -/
theorem ringedProjectionFormulaInverse_naturality
    (F G : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (P : StrictPerfectCoefficientPackage _ F) (P' : StrictPerfectCoefficientPackage _ G)
    (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r))
    (hb' : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (G.X r))
    (f : F ⟶ G) :
    RF.map (TS.map (CategoryTheory.Prod.mkHom (𝟙 E) (LF.map (DerivedCategory.Q.map f)))) ≫
      (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS hPR
        hPS TR
      TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE G P' hb').2 =
    (ringedProjectionFormulaArrows uInv uPush adj I c uStar hobj hmap LF epsilon hLF PR PS hPR hPS
      TR
      TS rR rS k V am RF eta hRF computeR computeL adjD canonicalAdj E K hK repE F P hb).2 ≫
      TR.map (CategoryTheory.Prod.mkHom (𝟙 (RF.obj E)) (DerivedCategory.Q.map f)) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  let LC := uStar.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  let A := VC.obj K
  let tensorR := curriedTensor (SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  let tensorS := curriedTensor (SheafOfModules.{u}
    ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  let hf := fun H P hb ↦ StrictPerfectCoefficientPackage.isKFlat_flat R H P hb
  let hR := fun H P hb ↦ (hPR H).mpr (hf H P hb)
  let hS := fun H P hb ↦ (hPS (LC.obj H)).mpr
    ((ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
      hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).1 H
        (hf H P hb).1 (hf H P hb).2)
  let unitData := canonicalRingedTensorComparison_unit R S RI uInv I c uStar hobj hmap k
  let j := Classical.choose unitData.exists
  have hj := Classical.choose_spec unitData.exists
  let t := fun H ↦ tensorAdjunctionTotal uStar V am k.mu k.naturality K H
  have htF : IsIso (t F) := tensorAdjunctionTotal_isIso uStar V am k.mu k.naturality
    j hj K F hb P.N P.i P.p P.splitting
  have htG : IsIso (t G) := tensorAdjunctionTotal_isIso uStar V am k.mu k.naturality
    j hj K G hb' P'.N P'.i P'.p P'.splitting
  let eL := fun H P hb ↦ @asIso _ _ _ _
    (derivedPullbackComplexComparison uStar LF epsilon H)
      (computeL H (hf H P hb).1 (hf H P hb).2)
  let eA : RF.obj E ≅ DerivedCategory.Q.obj A := RF.mapIso repE ≪≫
    (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta K) (computeR K hK)).symm
  let eC := fun H P hb ↦
    TR.mapIso (Iso.prod eA (Iso.refl (DerivedCategory.Q.obj H))) ≪≫
      mixedTensorRepresentative R PR hPR TR rR A H (hR H P hb)
  let J := fun H ↦ CochainComplex.mapBifunctor K (LC.obj H) tensorS
  have hJ (H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (P : StrictPerfectCoefficientPackage _ H)
      (hb : ∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (H.X r)) :
      (J H).IsKInjective := tensorAdjunctionTotal_target_isKInjective
    uStar j K hK H hb P.N P.i P.p P.splitting
  let inner := fun H P hb ↦ TS.mapIso (Iso.prod repE (eL H P hb)) ≪≫
    mixedTensorRepresentative S PS hPS TS rS K (LC.obj H) (hS H P hb)
  let eB := fun H P hb ↦ RF.mapIso (inner H P hb) ≪≫
        (@asIso _ _ _ _ (derivedPushforwardComplexComparison V RF eta (J H))
          (computeR (J H) (hJ H P hb))).symm
  let cf := HomologicalComplex.mapBifunctorMap (𝟙 A) f tensorR (.up ℤ)
  let jf := HomologicalComplex.mapBifunctorMap (𝟙 K) (LC.map f) tensorS (.up ℤ)
  let df := VC.map jf
  have hC : TR.map (CategoryTheory.Prod.mkHom (𝟙 (RF.obj E)) (DerivedCategory.Q.map f)) ≫
      (eC G P' hb').hom = (eC F P hb).hom ≫ DerivedCategory.Q.map cf := by
    simp only [eC, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    rw [← Category.assoc,
      CategoryTheory.map_prod_square TR eA.hom (𝟙 _) (𝟙 _)
        (DerivedCategory.Q.map f) (DerivedCategory.Q.map f) (by simp), Category.assoc]
    rw [mixedRepresentative_coefficient_naturality R PR hPR TR rR A F G
      (hR F P hb) (hR G P' hb') f]
    simp only [Category.assoc]
    rfl
  have hB : RF.map (TS.map
      (CategoryTheory.Prod.mkHom (𝟙 E) (LF.map (DerivedCategory.Q.map f)))) ≫
      (eB G P' hb').hom = (eB F P hb).hom ≫ DerivedCategory.Q.map df := by
    have hinner : TS.map
        (CategoryTheory.Prod.mkHom (𝟙 E) (LF.map (DerivedCategory.Q.map f))) ≫
        (inner G P' hb').hom = (inner F P hb).hom ≫ DerivedCategory.Q.map jf := by
      simp only [inner, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom]
      have hsquare := CategoryTheory.map_prod_square TS repE.hom
        (eL F P hb).hom (eL G P' hb').hom (LF.map (DerivedCategory.Q.map f))
        (DerivedCategory.Q.map (LC.map f))
        (CategoryTheory.pullback_naturality uStar LF epsilon f)
      rw [← Category.assoc, hsquare, Category.assoc]
      rw [mixedRepresentative_coefficient_naturality S PS hPS TS rS K
        (LC.obj F) (LC.obj G) (hS F P hb) (hS G P' hb') (LC.map f)]
      simp only [Category.assoc]
      rfl
    have : IsIso (derivedPushforwardComplexComparison V RF eta (J F)) :=
      computeR (J F) (hJ F P hb)
    have : IsIso (derivedPushforwardComplexComparison V RF eta (J G)) :=
      computeR (J G) (hJ G P' hb')
    have hinv := CategoryTheory.inverse_square _ _ _ _
      (CategoryTheory.pushforward_naturality V RF eta jf).symm
    dsimp only [eB, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [← RF.map_comp_assoc, hinner, RF.map_comp, Category.assoc, hinv]
    simp only [Category.assoc]
    rfl
  have ht : DerivedCategory.Q.map (t F) ≫ DerivedCategory.Q.map df =
      DerivedCategory.Q.map cf ≫ DerivedCategory.Q.map (t G) := by
    simpa only [← DerivedCategory.Q.map_comp] using congrArg DerivedCategory.Q.map
      (CategoryTheory.total_naturality uStar V am k.mu k.naturality K F G f).symm
  change _ ≫ ((eB G P' hb').hom ≫ DerivedCategory.Q.map (inv (t G)) ≫
      (eC G P' hb').inv) =
    ((eB F P hb).hom ≫ DerivedCategory.Q.map (inv (t F)) ≫ (eC F P hb).inv) ≫ _
  simpa only [Functor.map_inv] using CategoryTheory.transported_inverse_naturality
    (eC F P hb) (eC G P' hb') (eB F P hb) (eB G P' hb')
    (DerivedCategory.Q.map (t F)) (DerivedCategory.Q.map (t G)) _ _
    (DerivedCategory.Q.map cf) (DerivedCategory.Q.map df) hC hB ht

end SheafOfModules
