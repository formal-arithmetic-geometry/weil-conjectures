/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-!
# Restriction of the abelian derived exchange to bounded-below complexes
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem inverse_mate_app
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (β : TwoSquare R₁ H G R₂) (K : C₁) :
    ((mateEquiv adj₁ adj₂).symm β).natTrans.app K =
      L₂.map (G.map (adj₁.unit.app K) ≫ β.natTrans.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := by
  simp [mateEquiv]

private theorem inverse_mate_app_of_eq
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (hα : (mateEquiv adj₁ adj₂ α).natTrans = β.natTrans) (K : C₁) :
    α.natTrans.app K =
      L₂.map (G.map (adj₁.unit.app K) ≫ β.natTrans.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := by
  have hα' : mateEquiv adj₁ adj₂ α = β := hα
  rw [← (mateEquiv adj₁ adj₂).symm_apply_apply α, hα', inverse_mate_app]

private theorem inverse_mate_app_of_eq_three
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (α : TwoSquare G L₁ L₂ H) {J₁ J₂ : C₂ ⥤ C₃}
    (β₁ : R₁ ⋙ G ⟶ J₁) (β₂ : J₁ ⟶ J₂) (β₃ : J₂ ⟶ H ⋙ R₂)
    (hα : (mateEquiv adj₁ adj₂ α).natTrans = β₁ ≫ β₂ ≫ β₃) (K : C₁) :
    α.natTrans.app K =
      L₂.map (G.map (adj₁.unit.app K) ≫ β₁.app (L₁.obj K) ≫
        β₂.app (L₁.obj K) ≫ β₃.app (L₁.obj K)) ≫
        adj₂.counit.app (H.obj (L₁.obj K)) := by
  exact inverse_mate_app_of_eq adj₁ adj₂ α (β₁ ≫ β₂ ≫ β₃) hα K

private theorem restrict_exactDerivedAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    [EnoughInjectives D] {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    Adjunction.restrictFullyFaithful adj.mapDerivedCategoryRightDerivedAdjunction
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      L.mapDerivedCategoryPlusCompatibility.symm R.rightDerivedFunctorPlusCompatibility.symm =
      adj.derivedPlus := by
  apply Adjunction.ext
  apply Adjunction.derivedPlus_unit_eq
  intro K
  apply _root_.DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Adjunction.map_restrictFullyFaithful_unit_app]
  have h₁ := adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.Plus.ι _).obj K)
  have h₃ : R.rightDerivedFunctorPlusιUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app
        (_root_.DerivedCategory.Plus.Qh.obj (L.mapHomotopyCategoryPlus.obj K)) =
      R.ιRightDerivedFunctorUnit.app (L.mapHomotopyCategoryPlus.obj K) := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h₄ : _root_.DerivedCategory.Plus.ι.map
      (R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K)) =
      R.ιRightDerivedFunctorUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        R.rightDerivedFunctorPlusCompatibility.inv.app
          (_root_.DerivedCategory.Plus.Qh.obj (L.mapHomotopyCategoryPlus.obj K)) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₅ := R.rightDerivedFunctorPlusCompatibility.inv.naturality
    (L.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h₅
  have h₇ : _root_.DerivedCategory.Plus.ι.map
      (_root_.DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      _root_.DerivedCategory.Qh.map
        ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.Plus.ι _).obj K)) := by
    exact congrArg _root_.DerivedCategory.Qh.map
      (Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app adj K)
  rw [h₄, h₇]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.assoc, ← h₅, ← Category.assoc, h₁, Category.assoc]
  rfl

private noncomputable def exactComp {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W := a ≫ b) (hd : d = a ≫ b := by cat_disch) :
    D(upperStar AddCommGrpCat.{u + 1} d) ≅
      D(upperStar AddCommGrpCat.{u + 1} b) ⋙ D(upperStar AddCommGrpCat.{u + 1} a) :=
  Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} a b d hd) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem exactComp_conjugate {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W) (hd : d = a ≫ b) :
    (conjugateIsoEquiv (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} d)
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).comp
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a))
      (exactComp a b d hd).symm).symm =
      rightDerivedLowerStarComp AddCommGrpCat.{u + 1} a b ≪≫
        rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} hd.symm := by
  subst d
  simp only [rightDerivedLowerStarCongr_refl, Iso.trans_refl]
  rfl

private noncomputable def exactSquare {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f) :
    D(upperStar AddCommGrpCat.{u + 1} f) ⋙ D(upperStar AddCommGrpCat.{u + 1} h) ≅
      D(upperStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} e) :=
  (exactComp h f (e ≫ g) sq.w).symm ≪≫ exactComp e g

private noncomputable def exactExchange {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f) :
    R(lowerStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} f) ⟶
      D(upperStar AddCommGrpCat.{u + 1} e) ⋙ R(lowerStar AddCommGrpCat.{u + 1} h) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h)
    (TwoSquare.mk _ _ _ _ (exactSquare sq).hom)).natTrans

private theorem exactExchange_iterated {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f) :
    (mateEquiv (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e)
      (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
      (exactExchange sq)).natTrans =
      (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom ≫
        (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w).hom ≫
        (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv := by
  rw [exactExchange, iterated_mateEquiv_conjugateEquiv]
  change conjugateEquiv _ _ ((exactComp h f (e ≫ g) sq.w).inv ≫
    (exactComp e g).hom) = _
  rw [← conjugateEquiv_comp _
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (e ≫ g))]
  have hh := congrArg Iso.inv (exactComp_conjugate h f (e ≫ g) sq.w)
  have he := congrArg Iso.hom (exactComp_conjugate e g (e ≫ g) rfl)
  change conjugateEquiv _ _ (exactComp h f (e ≫ g) sq.w).inv = _ at hh
  change conjugateEquiv _ _ (exactComp e g).hom = _ at he
  rw [he, hh]
  simp only [rightDerivedLowerStarCongr_refl, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Category.comp_id]
  rfl

private theorem abelianDerivedBaseChangeArrow_eq_exactExchange {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    abelianDerivedBaseChangeArrow sq K = (exactExchange sq.toCommSq.flip).app K := by
  rfl

/-- Validation of the equivalent mate presentation used in the arrow definition. -/
private theorem abelianDerivedBaseChangeArrow_eq_pushforward_formula
    {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    abelianDerivedBaseChangeArrow sq K =
      D(upperStar AddCommGrpCat.{u + 1} f).map
        (R(lowerStar AddCommGrpCat.{u + 1} g).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e).unit.app K) ≫
          (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom.app _ ≫
          (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w.symm).hom.app _ ≫
          (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv.app _) ≫
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app _ := by
  rw [abelianDerivedBaseChangeArrow_eq_exactExchange]
  exact inverse_mate_app_of_eq_three
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (exactExchange sq.toCommSq.flip)
    (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom
    (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w.symm).hom
    (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv
    (exactExchange_iterated sq.toCommSq.flip) K

/-- The mate presentation retains the natural transformation landed by A4. -/
private theorem abelianDerivedBaseChangeTransformation_eq_pushforward
    {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g) :
    abelianDerivedBaseChangeTransformation sq =
      let E := D(upperStar AddCommGrpCat.{u + 1} e)
      let U := R(lowerStar AddCommGrpCat.{u + 1} e)
      let G := R(lowerStar AddCommGrpCat.{u + 1} g)
      let H := R(lowerStar AddCommGrpCat.{u + 1} h)
      let Q := R(lowerStar AddCommGrpCat.{u + 1} f)
      let F := D(upperStar AddCommGrpCat.{u + 1} f)
      let c : U ⋙ G ⟶ H ⋙ Q :=
        (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom ≫
          (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w.symm).hom ≫
          (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv
      let β : G ⟶ E ⋙ (H ⋙ Q) :=
        (Functor.leftUnitor G).inv ≫
          Functor.whiskerRight
            (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e).unit G ≫
          (Functor.associator E U G).hom ≫ Functor.whiskerLeft E c
      Functor.whiskerRight β F ≫ (Functor.associator E (H ⋙ Q) F).hom ≫
        Functor.whiskerLeft E ((Functor.associator H Q F).hom ≫
          Functor.whiskerLeft H
            (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit ≫
          (Functor.rightUnitor H).hom) := by
  ext K
  simpa only [abelianDerivedBaseChangeArrow, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Category.id_comp, Category.comp_id, Functor.map_comp, Functor.map_id, Category.assoc] using
    abelianDerivedBaseChangeArrow_eq_pushforward_formula sq K

private theorem map_exactComp_hom {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W) (hd : d = a ≫ b)
    (K : _root_.DerivedCategory.Plus (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    _root_.DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a b d hd).hom.app K) =
      (exactComp a b d hd).hom.app K.obj := by
  simp only [upperStarCompDerivedPlus, exactComp, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  rfl

private theorem map_exactComp_inv {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    (d : U ⟶ W) (hd : d = a ≫ b)
    (K : _root_.DerivedCategory.Plus (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    _root_.DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a b d hd).inv.app K) =
      (exactComp a b d hd).inv.app K.obj := by
  have he : _root_.DerivedCategory.Plus.ι.mapIso
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a b d hd).app K) =
      (exactComp a b d hd).app K.obj := Iso.ext (map_exactComp_hom a b d hd K)
  exact congrArg Iso.inv he

private theorem map_exactSquare {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f)
    (K : _root_.DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    _root_.DerivedCategory.Plus.ι.map
      ((pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom.app K) =
      (exactSquare sq).hom.app K.obj := by
  rw [pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    map_exactComp_inv, map_exactComp_hom, exactSquare]

private theorem map_derivedPlus_counit {X S : Scheme.{u}} (f : X ⟶ S)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    _root_.DerivedCategory.Plus.ι.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.counit.app K) =
      D(upperStar AddCommGrpCat.{u + 1} f).map
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app K.obj := by
  rw [← restrict_exactDerivedAdjunction
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f),
    Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  rfl

private theorem plusExchange_counit {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D+(upperStar AddCommGrpCat.{u + 1} h).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.counit.app
          (D+(upperStar AddCommGrpCat.{u + 1} e).obj K) =
      (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom.app
        (R+(lowerStar AddCommGrpCat.{u + 1} g).obj K) ≫
        D+(upperStar AddCommGrpCat.{u + 1} e).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).derivedPlus.counit.app K) := by
  have hh : (mateEquiv
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).derivedPlus
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus
      (TwoSquare.mk _ _ _ _
        (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom)).natTrans =
      derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq := by
    apply derivedBaseChangeMapPlus_ext
    intro M
    exact Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h)
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom)
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom)
      (pullbackSquareComparison_hom_app_factorsh AddCommGrpCat.{u + 1} sq) M
  rw [← hh]
  exact mateEquiv_counit _ _ _ K

private theorem exactExchange_counit {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f)
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D(upperStar AddCommGrpCat.{u + 1} h).map ((exactExchange sq).app K) ≫
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).counit.app
          (D(upperStar AddCommGrpCat.{u + 1} e).obj K) =
      (exactSquare sq).hom.app (R(lowerStar AddCommGrpCat.{u + 1} g).obj K) ≫
        D(upperStar AddCommGrpCat.{u + 1} e).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).counit.app K) :=
  mateEquiv_counit _ _ _ K

private theorem exactExchange_compatibility {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S} (sq : CommSq e h g f)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D(upperStar AddCommGrpCat.{u + 1} f).map
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (exactExchange sq).app K.obj =
      _root_.DerivedCategory.Plus.ι.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
        (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlusCompatibility.hom.app
          (D+(upperStar AddCommGrpCat.{u + 1} e).obj K) := by
  apply ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).homEquiv
    _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, exactExchange_counit, ← Functor.comp_map]
  erw [(exactSquare sq).hom.naturality_assoc]
  symm
  rw [Functor.map_comp, Category.assoc]
  erw [← map_derivedPlus_counit h]
  change _root_.DerivedCategory.Plus.ι.map
      (D+(upperStar AddCommGrpCat.{u + 1} h).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K)) ≫
      _root_.DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.counit.app
          (D+(upperStar AddCommGrpCat.{u + 1} e).obj K)) = _
  erw [← _root_.DerivedCategory.Plus.ι.map_comp, plusExchange_counit, Functor.map_comp,
    map_exactSquare]
  change _ ≫ D(upperStar AddCommGrpCat.{u + 1} e).map
    (_root_.DerivedCategory.Plus.ι.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).derivedPlus.counit.app K)) = _
  rw [map_derivedPlus_counit, Functor.map_comp]
  rfl

/-- The canonical unbounded abelian exchange restricts to the bounded-below exchange.
Source: blueprint sk-def-bc and the derived-adjunction construction, Stacks Project
Tag 0D6G (blueprint: lem-sbc-abelian-derived-exchange-plus-compatibility).

Proof: restrict the exact-inverse-image/right-derived-direct-image adjunction along the
fully faithful inclusions of bounded-below derived categories. The defining unit formula
on complexes identifies the restricted adjunction with the directly constructed one.
The inverse-image composition comparisons also restrict, since their natural-isomorphism
and composition factors do. Take adjoint transposes of the two exchange maps. Their
transposes are the square comparison followed by inverse image of the direct-image
counit. The counit restriction formula and naturality of the square comparison identify
these transposes, hence the maps. Cancel the invertible direct-image comparison on the
source to obtain the displayed formula. No geometric hypotheses beyond the given square
are needed. -/
theorem abelianDerivedBaseChangeArrow_eq_plus {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    abelianDerivedBaseChangeArrow sq K.obj =
      D(upperStar AddCommGrpCat.{u + 1} f).map
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
        _root_.DerivedCategory.Plus.ι.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq.flip).app K) ≫
        (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlusCompatibility.hom.app
          (D+(upperStar AddCommGrpCat.{u + 1} e).obj K) := by
  rw [abelianDerivedBaseChangeArrow_eq_exactExchange]
  apply (cancel_epi (D(upperStar AddCommGrpCat.{u + 1} f).map
    ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.hom.app K))).1
  rw [exactExchange_compatibility]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Etale
