/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.CategoryTheory.DerivedExactSquare
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Derived extension-by-zero base change

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
cor-cbc-derived-extension-zero-base-change; Stacks Tags 03S6, 0F70 and 015F
(blueprint: cor-cbc-derived-extension-zero-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

section DerivedTools

open CategoryTheory.Limits

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedNatIso_symm {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryPlusNatIso e.symm =
      (Functor.mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply DerivedCategory.Plus.ι.map_injective
  simp only [ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlusNatIso,
    Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, NatIso.mapHomologicalComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Iso.refl_symm, Iso.refl_trans,
    Functor.fullyFaithfulCancelRight_hom_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.refl_hom, NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.id_app,
    ObjectProperty.ι_map, Functor.fullyFaithfulCancelRight_inv_app, Iso.trans_inv,
    Iso.refl_inv, Functor.isoWhiskerLeft_inv, Category.id_comp]
  congr 2
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedSquare_symm
    {E F : Type*} [Category E] [Category F] [Abelian E] [Abelian F]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S) :
    Functor.mapDerivedCategoryPlusSquareIso L S R G q.symm =
      (Functor.mapDerivedCategoryPlusSquareIso R G L S q).symm := by
  simp only [Functor.mapDerivedCategoryPlusSquareIso, derivedNatIso_symm]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedComp_symm
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (q : H ≅ F ⋙ G) :
    (Functor.mapDerivedCategoryPlusCompIso F G).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso q.symm =
      (Functor.mapDerivedCategoryPlusNatIso q ≪≫
        Functor.mapDerivedCategoryPlusCompIso F G).symm := by
  simp only [derivedNatIso_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedId_fac (L : C ⥤ C) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : L ≅ 𝟭 C) (K : HomotopyCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
    L.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  rw [Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem square_identity
    (R : C ⥤ D) (G : D ⥤ D) (L : C ⥤ C)
    [R.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (q : R ⋙ G ≅ L ⋙ R) (eL : L ≅ 𝟭 C) (eG : G ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ R.map (eL.hom.app X) = eG.hom.app (R.obj X))
    (K : DerivedCategory.Plus C) :
    (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom.app K ≫
      R.mapDerivedCategoryPlus.map ((Functor.mapDerivedCategoryPlusNatIso eL ≪≫
        Functor.mapDerivedCategoryPlusIdIso C).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso eG ≪≫
        Functor.mapDerivedCategoryPlusIdIso D).hom.app (R.mapDerivedCategoryPlus.obj K) := by
  let eLD := Functor.mapDerivedCategoryPlusNatIso eL ≪≫
    Functor.mapDerivedCategoryPlusIdIso C
  let eGD := Functor.mapDerivedCategoryPlusNatIso eG ≪≫
    Functor.mapDerivedCategoryPlusIdIso D
  have hn : (Functor.mapDerivedCategoryPlusSquareIso R G L R q).hom ≫
      Functor.whiskerRight eLD.hom R.mapDerivedCategoryPlus =
      Functor.whiskerLeft R.mapDerivedCategoryPlus eGD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (R.mapDerivedCategoryPlusFactorsh.hom.app X)]
    have hnat := eGD.hom.naturality (R.mapDerivedCategoryPlusFactorsh.hom.app X)
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at hnat
    rw [Category.assoc, ← hnat]
    dsimp only [eLD, eGD]
    rw [derivedId_fac, derivedId_fac, Functor.map_comp, Category.assoc]
    have hnR := R.mapDerivedCategoryPlusFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategoryPlus eL.hom).app X)
    dsimp only [Functor.comp_map] at hnR
    erw [hnR]
    erw [reassoc_of% (Functor.mapDerivedCategoryPlusSquareIso_fac R G L R q X)]
    congr 2
    rw [← DerivedCategory.Plus.Qh.map_comp]
    congr 1
    apply (HomotopyCategory.Plus.ι D).map_injective
    simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    obtain ⟨⟨P⟩, hP⟩ := X
    change (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app P) ≫
      (R.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eL.hom (.up ℤ)).app P)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex eG.hom (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj P))
    rw [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext i
    exact hq (P.X i)
  exact NatTrans.congr_app hn K

end DerivedTools

section Underived

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

omit [HasSmallSiteSheafify A] in
private theorem mate_openBaseChange
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq gU j' j g) :
    mateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
        (openImmersionLowerShriekUpperStarAdjunction A j')
        (TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sq)) =
      TwoSquare.mk _ _ _ _ (squareUpperStarIso A sq.flip).hom := by
  exact mateEquiv_eq_of_unit _ _ _ _
    (fun F ↦ (unit_map_openImmersionLowerShriekBaseChangeMap_app A sq F).symm)

private theorem openBaseChange_horizontal
    {U' U X' X U'' X'' : Scheme.{u}}
    {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    {hU : U'' ⟶ U'} {j'' : U'' ⟶ X''} {h : X'' ⟶ X'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (sq : CommSq gU j' j g) (sq' : CommSq hU j'' j' h)
    (sq3 : CommSq (hU ≫ gU) j'' j (h ≫ g))
    (F : Sheaf U.smallEtaleTopology A) :
    (openImmersionLowerShriekBaseChangeMap A sq3).app F =
      ((j'')_!open[A]).map ((upperStarComp A hU gU).hom.app F) ≫
        (openImmersionLowerShriekBaseChangeMap A sq').app (((gU)^*[A]).obj F) ≫
        ((h)^*[A]).map ((openImmersionLowerShriekBaseChangeMap A sq).app F) ≫
        (upperStarComp A h g).inv.app (((j)_!open[A]).obj F) := by
  have hs : TwoSquare.mk _ _ _ _
      (openImmersionLowerShriekBaseChangeMap A sq3) =
      (((TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sq)).hComp
        (TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sq'))).whiskerTop
          (upperStarComp A hU gU).hom).whiskerBottom (upperStarComp A h g).inv := by
    apply (mateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
      (openImmersionLowerShriekUpperStarAdjunction A j'')).injective
    rw [mate_openBaseChange, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp,
      mate_openBaseChange, mate_openBaseChange]
    apply TwoSquare.ext
    intro M
    simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj, Category.assoc] using
      NatTrans.congr_app (squareUpperStarIso_paste_vert_hom A sq'.flip sq.flip
        sq3.flip) M
  simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    TwoSquare.hComp_app, Category.assoc] using congr_app hs F

set_option backward.isDefEq.respectTransparency false in
private theorem openBaseChange_identity
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology A) :
    (openImmersionLowerShriekBaseChangeMap A (IsPullback.id_horiz j).toCommSq).app F ≫
        (upperStarId A X).hom.app (((j)_!open[A]).obj F) =
      ((j)_!open[A]).map ((upperStarId A U).hom.app F) := by
  have hs : TwoSquare.mk _ _ _ _
      (openImmersionLowerShriekBaseChangeMap A (IsPullback.id_horiz j).toCommSq) =
      ((TwoSquare.hId ((j)_!open[A])).whiskerTop (upperStarId A U).hom).whiskerBottom
        (upperStarId A X).inv := by
    apply (mateEquiv (openImmersionLowerShriekUpperStarAdjunction A j)
      (openImmersionLowerShriekUpperStarAdjunction A j)).injective
    rw [mate_openBaseChange, mateEquiv_whiskerTop_whiskerBottom, TwoSquare.hId,
      mateEquiv_unitors]
    apply TwoSquare.ext
    intro M
    simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
      TwoSquare.mk, TwoSquare.natTrans]
    dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    have normalize (diag : U ⟶ X) (h₁ : diag = 𝟙 U ≫ j) (h₂ : diag = j ≫ 𝟙 X) :
        (upperStarComp A (𝟙 U) j diag h₁).inv.app M ≫
            (upperStarComp A j (𝟙 X) diag h₂).hom.app M =
          ((upperStarId A U).hom.app ((j)^*[A].obj M) ≫
            ((j)^*[A]).rightUnitor.hom.app M ≫ ((j)^*[A]).leftUnitor.inv.app M) ≫
              ((j)^*[A]).map ((upperStarId A X).inv.app M) := by
      have hd : diag = j := h₂.trans (Category.comp_id j)
      subst hd
      rw [upperStarComp_id_left, upperStarComp_id_right]
      simp
    exact normalize _ _ _
  have hv := congr_app hs F
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    TwoSquare.hId_app] at hv
  rw [hv]
  simp

omit [HasSmallSiteSheafify A] in
private theorem conjugate_openComp
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction A k).comp
          (openImmersionLowerShriekUpperStarAdjunction A j))
        (openImmersionLowerShriekUpperStarAdjunction A (k ≫ j))
        (openImmersionLowerShriekComp A k j) = (upperStarComp A k j).symm := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro F
  exact (Adjunction.unit_leftAdjointUniq_hom_app
    (openImmersionLowerShriekUpperStarAdjunction A (k ≫ j))
    (((openImmersionLowerShriekUpperStarAdjunction A k).comp
      (openImmersionLowerShriekUpperStarAdjunction A j)).ofNatIsoRight
        (upperStarComp A k j).symm) F).symm

private theorem openBaseChange_vertical
    {V' V U' U X' X : Scheme.{u}}
    {gV : V' ⟶ V} {k' : V' ⟶ U'} {k : V ⟶ U} {gU : U' ⟶ U}
    {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
    [IsOpenImmersion k] [IsOpenImmersion k']
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sqk : CommSq gV k' k gU) (sqj : CommSq gU j' j g)
    (sq : CommSq gV (k' ≫ j') (k ≫ j) g)
    (F : Sheaf V.smallEtaleTopology A) :
    (openImmersionLowerShriekBaseChangeMap A sq).app F =
      (openImmersionLowerShriekComp A k' j').hom.app (((gV)^*[A]).obj F) ≫
        ((j')_!open[A]).map ((openImmersionLowerShriekBaseChangeMap A sqk).app F) ≫
        (openImmersionLowerShriekBaseChangeMap A sqj).app (((k)_!open[A]).obj F) ≫
        ((g)^*[A]).map ((openImmersionLowerShriekComp A k j).inv.app F) := by
  have hs : TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sq) =
      (((TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sqk)).vComp
        (TwoSquare.mk _ _ _ _ (openImmersionLowerShriekBaseChangeMap A sqj))).whiskerRight
          (openImmersionLowerShriekComp A k' j').hom).whiskerLeft
            (openImmersionLowerShriekComp A k j).inv := by
    apply (mateEquiv (openImmersionLowerShriekUpperStarAdjunction A (k ≫ j))
      (openImmersionLowerShriekUpperStarAdjunction A (k' ≫ j'))).injective
    rw [mate_openBaseChange, conjugateEquiv_mateEquiv_vcomp _
      ((openImmersionLowerShriekUpperStarAdjunction A k).comp
        (openImmersionLowerShriekUpperStarAdjunction A j)),
      mateEquiv_conjugateEquiv_vcomp _
        ((openImmersionLowerShriekUpperStarAdjunction A k').comp
          (openImmersionLowerShriekUpperStarAdjunction A j')),
      mateEquiv_hcomp, mate_openBaseChange, mate_openBaseChange]
    have hc := congrArg Iso.inv (conjugate_openComp A k j)
    have hc' := congrArg Iso.hom (conjugate_openComp A k' j')
    change conjugateEquiv _ _ (openImmersionLowerShriekComp A k j).inv =
      (upperStarComp A k j).hom at hc
    change conjugateEquiv _ _ (openImmersionLowerShriekComp A k' j').hom =
      (upperStarComp A k' j').inv at hc'
    rw [hc, hc']
    apply TwoSquare.ext
    intro M
    simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using
      NatTrans.congr_app (squareUpperStarIso_paste_horiz_hom A sqj.flip sqk.flip sq.flip) M
  simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    TwoSquare.vComp_app, Category.assoc] using congr_app hs F

end Underived

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The inverse of the canonical adjunction mate, applied termwise and localized,
restricted to bounded below derived categories. Source: Stacks 03S6, 015F
(blueprint: cor-cbc-derived-extension-zero-base-change).
The `IsPullback` argument is the property underlying `OpenImmersionSquare`;
its chosen pullback identification does not affect this canonical map. -/
noncomputable def extensionZeroBaseChangeDerivedPlusIso
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((gU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
        (ModuleCat.{u + 1} Λ) sq)).symm ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical composition comparison for exact extension by zero on `D⁺`.
Source: Stacks 03D8 and 015F, obtained by localizing `openImmersionLowerShriekComp`
(blueprint: cor-cbc-derived-extension-zero-base-change). -/
noncomputable def extensionZeroCompDerivedPlusIso
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    ((k)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
        ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      ((k ≫ j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j).symm

private theorem extensionZeroBaseChangeDerivedPlusIso_symm
    {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    extensionZeroBaseChangeDerivedPlusIso Λ sq =
      (Functor.mapDerivedCategoryPlusSquareIso
        ((gU)^*[ModuleCat.{u + 1} Λ]) ((j')_!open[ModuleCat.{u + 1} Λ])
        ((j)_!open[ModuleCat.{u + 1} Λ]) ((g)^*[ModuleCat.{u + 1} Λ])
        (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq))).symm := by
  exact derivedSquare_symm _ _ _ _ _

private theorem extensionZeroCompDerivedPlusIso_symm
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    extensionZeroCompDerivedPlusIso Λ k j =
      (Functor.mapDerivedCategoryPlusNatIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k j) ≪≫
        Functor.mapDerivedCategoryPlusCompIso
          ((k)_!open[ModuleCat.{u + 1} Λ]) ((j)_!open[ModuleCat.{u + 1} Λ])).symm := by
  exact derivedComp_symm _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Derived extension-by-zero base change is invertible, natural, unital and compatible
with pasting in both directions. Source: blueprint cor-cbc-derived-extension-zero-base-change,
Stacks 03S6, 0F70, 015F (blueprint: cor-cbc-derived-extension-zero-base-change).

Proof plan: (1) Inverse image and extension by zero are additive exact functors
(prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-extension-by-zero-exact).
Their termwise functors preserve quasi-isomorphisms and cohomological lower bounds
(lem-weil-pbc-exact-functor-derived-factorization,
lem-weil-pbc-exact-functor-bounded-below), so all four functors act on D⁺.
(2) The underived exchange is the inverse of the mate of the unit and square
identification (lem-cbc-extension-zero-base-change,
def-weil-pbc-etale-shriek-base-change-map,
lem-weil-pbc-etale-shriek-base-change-modules). Its restriction is the identity by
lem-weil-pbc-extension-by-zero-adjunction and lem-weil-pbc-extension-by-zero-unit-iso.
The module-linear inverse-image comparisons are those of
lem-weil-pbc-inverse-image-composition-module-linear.
(3) Transpose the identity comparison under the extension-by-zero adjunction to get
the unit. For two successive base changes the transposes of the two inverse maps
coincide by naturality and associativity of inverse image
(lem-weil-pbc-derived-inverse-image-composition). Injectivity of the adjunction
bijection proves equality. For composable opens use the unit-compatible comparison
of left adjoints (lem-cbc-extension-zero-composition,
lem-weil-pbc-conjugate-iso-unit-equation, def-weil-pbc-composite-adjunction);
restriction gives identities and transposing the inverses again proves equality.
(4) Apply the sheaf exchange degreewise: naturality with the differentials gives
an isomorphism of complexes. Descend it through localization
(lem-weil-pbc-localization-universal-property), using the factorization comparisons
for each composite. This is precisely `extensionZeroBaseChangeDerivedPlusIso`.
(5) Localize the identity and both pasting equations degreewise. Localization
preserves their compositions; equality is detected on localized complexes by the
same universal property. Restrict to D⁺ to obtain the equations below. -/
theorem derivedExtensionZeroBaseChange [Finite Λ] :
    (∀ {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
      {j : U ⟶ X} {g : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : IsPullback gU j' j g),
      (∀ K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K)) ∧
      (∀ (K L : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
            (t : K ⟶ L),
        (((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙ ((g)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus).map t ≫
            (extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app L =
          (extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K ≫
            (((gU)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙ ((j')_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus).map t)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (IsPullback.id_horiz j)).hom.app K ≫
          ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map ((upperStarIdDerivedPlus
            (ModuleCat.{u + 1} Λ) U).hom.app K) =
        (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).hom.app (((j)_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {U' U X' X U'' X'' : Scheme.{u}}
      {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      {hU : U'' ⟶ U'} {j'' : U'' ⟶ X''} {h : X'' ⟶ X'}
      [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
      (sq : IsPullback gU j' j g) (sq' : IsPullback hU j'' j' h)
      (K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (sq'.paste_horiz sq)).hom.app K =
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) h g).hom.app (((j)_!open[ModuleCat.{u +
            1} Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K) ≫
          (extensionZeroBaseChangeDerivedPlusIso Λ sq').hom.app (((gU)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((j'')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) hU gU).inv.app K)) ∧
    (∀ {V' V U' U X' X : Scheme.{u}}
      {gV : V' ⟶ V} {k' : V' ⟶ U'} {k : V ⟶ U} {gU : U' ⟶ U}
      {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}
      [IsOpenImmersion k] [IsOpenImmersion k']
      [IsOpenImmersion j] [IsOpenImmersion j']
      (sqk : IsPullback gV k' k gU) (sqj : IsPullback gU j' j g)
      (K : _root_.DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroBaseChangeDerivedPlusIso Λ (sqk.paste_vert sqj)).hom.app K =
        ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map ((extensionZeroCompDerivedPlusIso
            Λ k j).inv.app K) ≫
          (extensionZeroBaseChangeDerivedPlusIso Λ sqj).hom.app (((k)_!open[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K) ≫
          ((j')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
            ((extensionZeroBaseChangeDerivedPlusIso Λ sqk).hom.app K) ≫
          (extensionZeroCompDerivedPlusIso Λ k' j').hom.app (((gV)^*[ModuleCat.{u + 1}
            Λ]).mapDerivedCategoryPlus.obj K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U' U X' X gU j' j g _ _ sq
    exact ⟨fun K ↦ inferInstance, fun K L t ↦
      (extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.naturality t⟩
  · intro U X j _ K
    let A := ModuleCat.{u + 1} Λ
    let q := (@asIso _ _ _ _ _
      (isIso_openImmersionLowerShriekBaseChangeMap A (IsPullback.id_horiz j))).symm
    apply square_identity ((j)_!open[A]) ((𝟙 X)^*[A]) ((𝟙 U)^*[A]) q
      (upperStarId A U) (upperStarId A X) _ K
    intro F
    apply (cancel_epi (q.inv.app F)).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact (openBaseChange_identity A j F).symm
  · intro U' U X' X U'' X'' gU j' j g hU j'' h _ _ _ sq sq' K
    let A := ModuleCat.{u + 1} Λ
    let q := (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq)).symm
    let q' := (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sq')).symm
    let q'' := (@asIso _ _ _ _ _
      (isIso_openImmersionLowerShriekBaseChangeMap A (sq'.paste_horiz sq))).symm
    have hq (F : Sheaf U.smallEtaleTopology A) :
        q''.hom.app F ≫ ((j'')_!open[A]).map ((upperStarComp A hU gU).hom.app F) =
          (upperStarComp A h g).hom.app (((j)_!open[A]).obj F) ≫
            ((h)^*[A]).map (q.hom.app F) ≫ q'.hom.app (((gU)^*[A]).obj F) := by
      apply (cancel_epi (q''.inv.app F)).mp
      dsimp only [q, q', q'', Iso.symm_hom, Iso.symm_inv]
      rw [Iso.hom_inv_id_app_assoc]
      simp only [asIso_hom]
      rw [openBaseChange_horizontal A sq.toCommSq sq'.toCommSq
          (sq'.paste_horiz sq).toCommSq]
      simp [Category.assoc]
    have hd := Functor.mapDerivedCategoryPlusSquareIso_comp
      ((gU)^*[A]) ((hU)^*[A]) ((hU ≫ gU)^*[A])
      ((g)^*[A]) ((h)^*[A]) ((h ≫ g)^*[A])
      ((j)_!open[A]) ((j')_!open[A]) ((j'')_!open[A])
      q q' q'' (upperStarComp A hU gU) (upperStarComp A h g) hq K
    change (extensionZeroBaseChangeDerivedPlusIso Λ (sq'.paste_horiz sq)).hom.app K ≫
      ((j'')_!open[A]).mapDerivedCategoryPlus.map
        ((upperStarCompDerivedPlus A hU gU).hom.app K) =
      (upperStarCompDerivedPlus A h g).hom.app
          (((j)_!open[A]).mapDerivedCategoryPlus.obj K) ≫
        ((h)^*[A]).mapDerivedCategoryPlus.map
          ((extensionZeroBaseChangeDerivedPlusIso Λ sq).hom.app K) ≫
        (extensionZeroBaseChangeDerivedPlusIso Λ sq').hom.app
          (((gU)^*[A]).mapDerivedCategoryPlus.obj K) at hd
    dsimp only [A] at hd ⊢
    rw [← cancel_mono (((j'')_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) hU gU).hom.app K))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    simp only [Functor.comp_obj] at hd ⊢
    erw [CategoryTheory.Category.comp_id]
    exact hd
  · intro V' V U' U X' X gV k' k gU j' j g _ _ _ _ sqk sqj K
    let A := ModuleCat.{u + 1} Λ
    let qk := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sqk)
    let qj := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A sqj)
    let q := @asIso _ _ _ _ _
      (isIso_openImmersionLowerShriekBaseChangeMap A (sqk.paste_vert sqj))
    have hq (F : Sheaf V.smallEtaleTopology A) :
        q.hom.app F ≫ ((g)^*[A]).map ((openImmersionLowerShriekComp A k j).hom.app F) =
          (openImmersionLowerShriekComp A k' j').hom.app (((gV)^*[A]).obj F) ≫
            ((j')_!open[A]).map (qk.hom.app F) ≫ qj.hom.app (((k)_!open[A]).obj F) := by
      dsimp only [q, qk, qj, asIso_hom]
      rw [openBaseChange_vertical A sqk.toCommSq sqj.toCommSq
        (sqk.paste_vert sqj).toCommSq]
      simp [Category.assoc, ← Functor.map_comp]
    have hd := Functor.mapDerivedCategoryPlusSquareIso_comp
      ((k)_!open[A]) ((j)_!open[A]) ((k ≫ j)_!open[A])
      ((k')_!open[A]) ((j')_!open[A]) ((k' ≫ j')_!open[A])
      ((gV)^*[A]) ((gU)^*[A]) ((g)^*[A]) qk qj q
      (openImmersionLowerShriekComp A k j) (openImmersionLowerShriekComp A k' j') hq K
    have hk := congrArg Iso.inv (extensionZeroCompDerivedPlusIso_symm Λ k j)
    have hk' := congrArg Iso.inv (extensionZeroCompDerivedPlusIso_symm Λ k' j')
    simp only [Iso.symm_inv] at hk hk'
    dsimp only [q, qk, qj, A] at hd
    have hbk := congrArg Iso.inv (extensionZeroBaseChangeDerivedPlusIso_symm Λ sqk)
    have hbj := congrArg Iso.inv (extensionZeroBaseChangeDerivedPlusIso_symm Λ sqj)
    have hb := congrArg Iso.inv
      (extensionZeroBaseChangeDerivedPlusIso_symm Λ (sqk.paste_vert sqj))
    simp only [Iso.symm_inv] at hbk hbj hb
    rw [← hbk, ← hbj, ← hb, ← hk, ← hk'] at hd
    apply (cancel_epi
      ((extensionZeroBaseChangeDerivedPlusIso Λ (sqk.paste_vert sqj)).inv.app K)).mp
    rw [Iso.inv_hom_id_app]
    rw [reassoc_of% hd]
    simp [← Functor.map_comp_assoc]


end AlgebraicGeometry.Etale
