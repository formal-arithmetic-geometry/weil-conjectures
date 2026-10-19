/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleComplexPullbackTransport
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import Sheaf.CategoryTheory.DerivedExactSquare
import WeilConjectures.CategoryTheory.RightDerivedPlusCube

/-! # Derived cohomology and passage to underlying abelian sheaves

Source: Stacks Project, Tag 03FD (cohomology of modules and underlying abelian sheaves),
and Tags 03D3 and 03D7 (inverse image and its adjunction).
(blueprint: lem-weil-pbc-derived-module-underlying-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Canonical restriction for module-valued derived cohomology, including the
composition comparison for pullbacks. This is the same three-factor map used in
`derived_cohomology_continuity`.
(blueprint: lem-weil-pbc-derived-module-underlying-comparison). -/
noncomputable def moduleDerivedRestriction (Λ : Type (u + 1)) [CommRing Λ]
    {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    (cohomology (ModuleCat.{u + 1} Λ) Y n).obj
      ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj K) ⟶
    (cohomology (ModuleCat.{u + 1} Λ) X n).obj
      ((upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory.obj K) :=
  (cohomology (ModuleCat.{u + 1} Λ) Y n).map
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
      ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj K)) ≫
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) f).hom.app
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.obj K))) ≫
  (cohomology (ModuleCat.{u + 1} Λ) X n).map
    ((Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} Λ) f g h hh) ≪≫
      Functor.mapDerivedCategoryCompIso
        (upperStar (ModuleCat.{u + 1} Λ) g)
        (upperStar (ModuleCat.{u + 1} Λ) f)).inv.app K)

instance moduleUnderlying_preservesFiniteColimits
    (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
  have : PreservesColimitsOfSize.{0, 0}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    (ModuleCat.forget₂CoinduceAdj Λ).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The exact underlying-abelian-sheaf functor. -/
noncomputable abbrev moduleUnderlyingSheaf (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance moduleUnderlyingSheaf_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : PreservesFiniteLimits (moduleUnderlyingSheaf Λ X) := by
  have : PreservesFiniteLimits (moduleUnderlyingSheaf Λ X ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance moduleUnderlyingSheaf_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) : PreservesFiniteColimits (moduleUnderlyingSheaf Λ X) := by
  let : (moduleUnderlyingSheaf Λ X).IsLeftAdjoint :=
    (Sheaf.forget₂CoinduceAdj X.smallEtaleTopology Λ).isLeftAdjoint
  infer_instance

/-- Sections commute with passage to underlying abelian sheaves. -/
noncomputable def moduleUnderlyingSectionsIso (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :
    Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
    moduleUnderlyingSheaf Λ X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal) _ ≪≫
    Functor.isoWhiskerLeft (moduleUnderlyingSheaf Λ X)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).symm

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingSections_pullback
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) ≫
      (moduleUnderlyingSectionsIso Λ X).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) =
    (moduleUnderlyingSectionsIso Λ Y).hom.app G ≫
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
        ((moduleUnderlyingSheaf Λ Y).obj G) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (upperStarForget₂Comparison Λ f G) := by
  simp only [globalSectionsUpperStarMap, moduleUnderlyingSectionsIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  have he := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).inv.naturality
      (upperStarForget₂Comparison Λ f G)
  rw [← he]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (upperStarForget₂Comparison Λ f G).hom.naturality
    (PreservesTerminal.iso f.Etale).inv.op
  change _ = _ ≫ _ ≫ _ ≫
    (upperStarForget₂Comparison Λ f G).hom.app (Opposite.op (⊤_ X.Etale)) ≫ _
  rw [reassoc_of% hn]
  have hu := congrArg
    (fun k ↦ k.hom.app (Opposite.op (⊤_ Y.Etale)))
    (unit_comp_lowerStar_map_upperStarForget₂Comparison Λ f G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((moduleUnderlyingSheaf Λ Y).obj G)).hom.app (Opposite.op (⊤_ Y.Etale)) ≫
      (upperStarForget₂Comparison Λ f G).hom.app
        (Opposite.op (f.Etale.obj (⊤_ Y.Etale))) =
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G).hom.app
        (Opposite.op (⊤_ Y.Etale))) at hu
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hu]
  rfl

private noncomputable def sectionsPullbackNat
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.Γ Y.smallEtaleTopology A ⋙ 𝟭 A ⟶
      upperStar A f ⋙ Sheaf.Γ X.smallEtaleTopology A :=
  (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (upperStarLowerStarAdjunction A f).unit
      (Sheaf.Γ Y.smallEtaleTopology A) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (lowerStarCompGlobalSectionsIso A f).hom

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsPullbackNat_app
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Sheaf Y.smallEtaleTopology A) :
    (sectionsPullbackNat A f).app G = globalSectionsUpperStarMap A f G := by
  simp only [sectionsPullbackNat, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, lowerStarCompGlobalSectionsIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom]
  have hn := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
    terminalIsTerminal).hom.naturality ((upperStarLowerStarAdjunction A f).unit.app G)
  rw [reassoc_of% hn]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingSections_cube
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((sectionsPullbackNat (ModuleCat.{u + 1} Λ) f).app G) ≫
      (moduleUnderlyingSectionsIso Λ X).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((asIso (upperStarForget₂ Λ f).natTrans).inv.app G) =
    (moduleUnderlyingSectionsIso Λ Y).hom.app G ≫
      (sectionsPullbackNat AddCommGrpCat.{u + 1} f).app
        ((moduleUnderlyingSheaf Λ Y).obj G) := by
  have he := underlyingSections_pullback Λ f G
  rw [← sectionsPullbackNat_app, ← sectionsPullbackNat_app] at he
  have hd : (asIso (upperStarForget₂ Λ f).natTrans).hom.app G =
      upperStarForget₂Comparison Λ f G := upperStarForget₂_natTrans_app Λ f G
  rw [← hd] at he
  rw [← Category.assoc, he, Category.assoc, Category.assoc, ← Functor.map_comp]
  rw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingPullback_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    upperStarForget₂Comparison Λ h' L ≫
        (moduleUnderlyingSheaf Λ Y').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L) =
      (upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
          ((moduleUnderlyingSheaf Λ S).obj L) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map
          (upperStarForget₂Comparison Λ h L) ≫
        upperStarForget₂Comparison Λ a
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)  := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h').homEquiv _ _ |>.injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, unit_comp_lowerStar_map_upperStarForget₂Comparison Λ h' L]
  change (moduleUnderlyingSheaf Λ S).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h').unit.app L) ≫
      (moduleUnderlyingSheaf Λ S).map
        ((lowerStar (ModuleCat.{u + 1} Λ) h').map
          ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app L)) = _
  rw [← Functor.map_comp,
    upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) a h L h' w.symm]
  rw [Functor.map_comp]
  rw [reassoc_of% (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} a h
    ((moduleUnderlyingSheaf Λ S).obj L) h' w.symm)]
  rw [reassoc_of% ((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} a).map
      (upperStarForget₂Comparison Λ h L))).symm]
  erw [((lowerStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.naturality
    (upperStarForget₂Comparison Λ a
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L))).symm]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
  have hn := congrArg (lowerStar AddCommGrpCat.{u + 1} h).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.naturality
      (upperStarForget₂Comparison Λ h L))
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
  rw [reassoc_of% hn.symm]
  rw [← (lowerStar AddCommGrpCat.{u + 1} h).map_comp_assoc
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app
      ((moduleUnderlyingSheaf Λ Y).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))
    ((lowerStar AddCommGrpCat.{u + 1} a).map
      (upperStarForget₂Comparison Λ a
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)))]
  rw [unit_comp_lowerStar_map_upperStarForget₂Comparison Λ a
    ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)]
  rw [reassoc_of% (unit_comp_lowerStar_map_upperStarForget₂Comparison Λ h L)]
  rfl


/-- The canonical coefficient comparison for exact bounded-below pullback. -/
noncomputable def moduleUnderlyingPullbackDerivedIso
    (Λ : Type (u + 1)) [CommRing Λ] {X T : Scheme.{u}} (p : X ⟶ T) :
    (moduleUnderlyingSheaf Λ T).mapDerivedCategoryPlus ⋙
      (upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryPlus ≅
    (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⋙
      (moduleUnderlyingSheaf Λ X).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusSquareIso
    (moduleUnderlyingSheaf Λ T) (upperStar AddCommGrpCat.{u + 1} p)
    (upperStar (ModuleCat.{u + 1} Λ) p) (moduleUnderlyingSheaf Λ X)
    (asIso (upperStarForget₂ Λ p).natTrans)

attribute [irreducible] moduleUnderlyingPullbackDerivedIso

private noncomputable def underlyingPlusPullbackComp
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T)
    (hh : h = f ≫ g) :
    (upperStar A h).mapDerivedCategoryPlus ≅
      (upperStar A g).mapDerivedCategoryPlus ⋙ (upperStar A f).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso (upperStarComp A f g h hh) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (upperStar A g) (upperStar A f)

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingPlusPullbackComp_inv
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T)
    (hh : h = f ≫ g) (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology A)) :
    DerivedCategory.Plus.ι.map ((underlyingPlusPullbackComp A f g h hh).inv.app K) =
    (Functor.mapDerivedCategoryNatIso (upperStarComp A f g h hh) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar A g) (upperStar A f)).inv.app K.obj := by
  have he : DerivedCategory.Plus.ι.mapIso
      ((underlyingPlusPullbackComp A f g h hh).app K) =
      (Functor.mapDerivedCategoryNatIso (upperStarComp A f g h hh) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar A g) (upperStar A f)).app K.obj := by
    apply Iso.ext
    change DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusNatIso (upperStarComp A f g h hh)).hom.app K ≫
          (Functor.mapDerivedCategoryPlusCompIso (upperStar A g) (upperStar A f)).hom.app K) =
      (Functor.mapDerivedCategoryNatIso (upperStarComp A f g h hh)).hom.app K.obj ≫
        (Functor.mapDerivedCategoryCompIso (upperStar A g) (upperStar A f)).hom.app K.obj
    rw [Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  exact congrArg Iso.inv he

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingPullbackDerived_composition
    (Λ : Type (u + 1)) [CommRing Λ] {X Y T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = f ≫ g)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (moduleUnderlyingPullbackDerivedIso Λ h).hom.app K ≫
        (moduleUnderlyingSheaf Λ X).mapDerivedCategoryPlus.map
          ((underlyingPlusPullbackComp (ModuleCat.{u + 1} Λ) f g h hh).hom.app K) =
      (underlyingPlusPullbackComp AddCommGrpCat.{u + 1} f g h hh).hom.app
          ((moduleUnderlyingSheaf Λ T).mapDerivedCategoryPlus.obj K) ≫
        (upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.map
          ((moduleUnderlyingPullbackDerivedIso Λ g).hom.app K) ≫
        (moduleUnderlyingPullbackDerivedIso Λ f).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj K) := by
  unfold moduleUnderlyingPullbackDerivedIso
  exact Functor.mapDerivedCategoryPlusSquareIso_comp
    (upperStar (ModuleCat.{u + 1} Λ) g) (upperStar (ModuleCat.{u + 1} Λ) f)
    (upperStar (ModuleCat.{u + 1} Λ) h)
    (upperStar AddCommGrpCat.{u + 1} g) (upperStar AddCommGrpCat.{u + 1} f)
    (upperStar AddCommGrpCat.{u + 1} h)
    (moduleUnderlyingSheaf Λ T) (moduleUnderlyingSheaf Λ Y) (moduleUnderlyingSheaf Λ X)
    (asIso (upperStarForget₂ Λ g).natTrans) (asIso (upperStarForget₂ Λ f).natTrans)
    (asIso (upperStarForget₂ Λ h).natTrans)
    (upperStarComp (ModuleCat.{u + 1} Λ) f g h hh)
    (upperStarComp AddCommGrpCat.{u + 1} f g h hh)
    (fun L ↦ by
      simp only [asIso_hom, upperStarForget₂_natTrans_app]
      exact underlyingPullback_composition Λ f g h hh.symm L) K

/-- Underlying groups of derived sections, before taking homology. -/
noncomputable def moduleUnderlyingGlobalSectionsIso
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlus ⋙
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus ≅
    (moduleUnderlyingSheaf Λ X).mapDerivedCategoryPlus ⋙
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let GA := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hacy (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G] :
      GA.rightAcyclic ((moduleUnderlyingSheaf Λ X).obj G) :=
    fun m ↦ Scheme.isZero_rightDerived_globalSections_forget_of_injective X Λ G m
  have := Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (G := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G' := GA) (β := moduleUnderlyingSheaf Λ X) (γ := U)
    (moduleUnderlyingSectionsIso Λ X) hacy
  exact asIso (Functor.rightDerivedFunctorPlusBaseChange
    (G := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G' := GA) (β := moduleUnderlyingSheaf Λ X) (γ := U)
    (moduleUnderlyingSectionsIso Λ X).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingDerivedSections_cube
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let c : U ⋙ 𝟭 AddCommGrpCat.{u + 1} ≅ 𝟭 (ModuleCat.{u + 1} Λ) ⋙ U :=
      U.rightUnitor ≪≫ U.leftUnitor.symm
    let dc := (Functor.mapDerivedCategoryPlusCompIso U (𝟭 AddCommGrpCat.{u + 1})).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso c ≪≫
      Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u + 1} Λ)) U
    U.mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (sectionsPullbackNat (ModuleCat.{u + 1} Λ) f)).app K) ≫
      (moduleUnderlyingGlobalSectionsIso Λ X).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj K) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((moduleUnderlyingPullbackDerivedIso Λ f).inv.app K) =
    dc.inv.app
        ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlus.obj K) ≫
      (𝟭 AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
        ((moduleUnderlyingGlobalSectionsIso Λ Y).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange
        (sectionsPullbackNat AddCommGrpCat.{u + 1} f)).app
          ((moduleUnderlyingSheaf Λ Y).mapDerivedCategoryPlus.obj K) := by
  unfold moduleUnderlyingPullbackDerivedIso Functor.mapDerivedCategoryPlusSquareIso
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let c : U ⋙ 𝟭 AddCommGrpCat.{u + 1} ≅ 𝟭 (ModuleCat.{u + 1} Λ) ⋙ U :=
    U.rightUnitor ≪≫ U.leftUnitor.symm
  apply Functor.rightDerivedFunctorPlusBaseChange_cube
    (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (upperStar (ModuleCat.{u + 1} Λ) f) (𝟭 (ModuleCat.{u + 1} Λ))
    (upperStar AddCommGrpCat.{u + 1} f) (𝟭 AddCommGrpCat.{u + 1})
    (moduleUnderlyingSheaf Λ Y) U (moduleUnderlyingSheaf Λ X) U
    (sectionsPullbackNat (ModuleCat.{u + 1} Λ) f)
    (sectionsPullbackNat AddCommGrpCat.{u + 1} f)
    (moduleUnderlyingSectionsIso Λ Y).hom (moduleUnderlyingSectionsIso Λ X).hom
    c (asIso (upperStarForget₂ Λ f).natTrans)
  intro G
  dsimp only [c, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.id_map]
  erw [Category.id_comp]
  exact underlyingSections_cube Λ f G

private noncomputable def plusSectionsPullbackNat
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorPlus ⟶
      (upperStar A f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlus :=
  Functor.whiskerLeft (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorPlus
      (Functor.mapDerivedCategoryPlusIdIso A).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange (sectionsPullbackNat A f)

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingNatIso_refl (Λ : Type (u + 1)) [CommRing Λ] :
    Functor.mapDerivedCategoryPlusNatIso
      (Iso.refl (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) =
    Iso.refl (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{u + 1} Λ))
  intro M
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  apply (cancel_mono (U.mapDerivedCategoryPlusFactorsh.hom.app M)).mp
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [Iso.refl_hom, NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem underlyingDerivedSections_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
        ((plusSectionsPullbackNat (ModuleCat.{u + 1} Λ) f).app K) ≫
      (moduleUnderlyingGlobalSectionsIso Λ X).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj K) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((moduleUnderlyingPullbackDerivedIso Λ f).inv.app K) =
    (moduleUnderlyingGlobalSectionsIso Λ Y).hom.app K ≫
      (plusSectionsPullbackNat AddCommGrpCat.{u + 1} f).app
        ((moduleUnderlyingSheaf Λ Y).mapDerivedCategoryPlus.obj K) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let c : U ⋙ 𝟭 AddCommGrpCat.{u + 1} ≅ 𝟭 (ModuleCat.{u + 1} Λ) ⋙ U :=
    U.rightUnitor ≪≫ U.leftUnitor.symm
  have hc : c = Iso.refl U := by
    apply Iso.ext
    ext G
    rfl
  have h := underlyingDerivedSections_cube Λ f K
  dsimp only at h
  rw [show (U.rightUnitor ≪≫ U.leftUnitor.symm) = Iso.refl U from hc,
    underlyingNatIso_refl] at h
  simp only [plusSectionsPullbackNat, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [h]
  let M := (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlus.obj K
  have hL := congr_app (Functor.mapDerivedCategoryPlusCompIso_id_comp U) M
  have hLi : (Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u + 1} Λ)) U).inv.app M =
      U.mapDerivedCategoryPlus.map
        ((Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).hom.app M) := by
    apply (cancel_epi
      ((Functor.mapDerivedCategoryPlusCompIso (𝟭 (ModuleCat.{u + 1} Λ)) U).hom.app M)).mp
    exact (Iso.hom_inv_id_app _ M).trans hL.symm
  have hR := congr_app (Functor.mapDerivedCategoryPlusCompIso_comp_id U) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hR
  have hRh : (Functor.mapDerivedCategoryPlusCompIso U (𝟭 AddCommGrpCat.{u + 1})).hom.app M =
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).inv.app
        (U.mapDerivedCategoryPlus.obj M) := by
    apply (cancel_mono
      ((Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).hom.app
        (U.mapDerivedCategoryPlus.obj M))).mp
    exact hR.trans (Iso.inv_hom_id_app
      (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1})
      (U.mapDerivedCategoryPlus.obj M)).symm
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app]
  erw [Category.comp_id]
  rw [hLi, hRh]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).inv.naturality
    ((moduleUnderlyingGlobalSectionsIso Λ Y).hom.app K)
  simpa only [Functor.id_map, Category.assoc] using
    ((reassoc_of% hn) _).symm

set_option maxHeartbeats 1000000 in
-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionsPullbackDerivedNat
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rightDerivedGlobalSections A Y ⟶
      (upperStar A f).mapDerivedCategory ⋙ rightDerivedGlobalSections A X :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (mapDerivedUpperStarLowerStarAdjunction A f).unit
      (rightDerivedGlobalSections A Y) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem sectionsPullbackDerivedNat_fac
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorUnit.app M ≫
      (sectionsPullbackDerivedNat A f).app (DerivedCategory.Qh.obj M) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (sectionsPullbackNat A f) (.up ℤ)).app M) ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app
        (((upperStar A f).mapHomotopyCategory (.up ℤ)).obj M) ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor.map
        ((upperStar A f).mapDerivedCategoryFactorsh.inv.app M) := by
  let L := upperStar A f
  let R := lowerStar A f
  let G := Sheaf.Γ Y.smallEtaleTopology A
  let H := Sheaf.Γ X.smallEtaleTopology A
  let adj := upperStarLowerStarAdjunction A f
  let e := lowerStarCompGlobalSectionsIso A f
  let ell := rightDerivedLowerStarCompRightDerivedGlobalSectionsIso A f
  have hu : (mapDerivedUpperStarLowerStarAdjunction A f).unit.app
        (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app M) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj M) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app M) := by
    have hf := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit M
    change _ ≫ R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app M) = _ at hf
    rw [← Category.assoc, ← hf, Category.assoc, ← Functor.map_comp]
    simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  simp only [sectionsPullbackDerivedNat, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp]
  rw [hu, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  have hn := ell.hom.naturality (L.mapDerivedCategoryFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  erw [hn]
  have hG := G.rightDerivedFunctorUnit.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).unit.app M)
  simp only [Functor.comp_map] at hG
  erw [← reassoc_of% hG]
  have hcomp : (Functor.rightDerivedFunctorCompUnit R G).app
      ((L.mapHomotopyCategory (.up ℤ)).obj M) =
      G.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj
        ((L.mapHomotopyCategory (.up ℤ)).obj M)) ≫
        G.rightDerivedFunctor.map
          (R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj M)) := by
    have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).inv.app
        ((L.mapHomotopyCategory (.up ℤ)).obj M) = 𝟙 _ := by
      have h := Iso.inv_hom_id_app
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ))
        ((L.mapHomotopyCategory (.up ℤ)).obj M)
      erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
      exact h
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, hi]
    erw [DerivedCategory.Qh.map_id]
    dsimp
    simp only [Category.id_comp, Category.comp_id]
  erw [← reassoc_of% hcomp]
  have hfac : (R ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso R G).hom =
      Functor.rightDerivedFunctorCompUnit R G := by
    simp [Functor.rightDerivedFunctorCompIso]
  have hc0 : Functor.rightDerivedFunctorCompUnit R G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' R G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
    rw [← hfac, Category.assoc, ← Functor.whiskerLeft_comp]
    simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc]
    exact Functor.rightDerivedNatTrans_fac _ _ _ _
      (HomotopyCategory.quasiIso _ (.up ℤ)) _
  have hc := congr_app hc0 ((L.mapHomotopyCategory (.up ℤ)).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  erw [reassoc_of% hc]
  rw [← Functor.map_comp_assoc]
  congr 2
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map]
  simp only [NatTrans.mapHomotopyCategory_app]
  rw [← Functor.map_comp]
  congr 1
  ext j
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
    sectionsPullbackNat, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem plusSectionsPullbackNat_fac
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : HomotopyCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
    (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorPlusUnit.app M ≫
      (plusSectionsPullbackNat A f).app (DerivedCategory.Plus.Qh.obj M) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
        (sectionsPullbackNat A f)).app M) ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusUnit.app
        ((upperStar A f).mapHomotopyCategoryPlus.obj M) ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlus.map
        ((upperStar A f).mapDerivedCategoryPlusFactorsh.inv.app M) := by
  let G := Sheaf.Γ Y.smallEtaleTopology A
  let H := Sheaf.Γ X.smallEtaleTopology A
  let L := upperStar A f
  have hn := (Functor.mapDerivedCategoryPlusIdIso A).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app M)
  simp only [plusSectionsPullbackNat, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [← Category.assoc, hn, Category.assoc]
  have hb := congr_app
    (Functor.rightDerivedFunctorPlusBaseChange_fac (sectionsPullbackNat A f)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hb
  erw [hb]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, CategoryTheory.Functor.map_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  simp only [← Category.assoc]
  erw [Iso.inv_hom_id_app, Category.id_comp, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsCompatibility_fac
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    (X : Scheme.{u}) (M : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.Plus.ι.map
        ((Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusUnit.app M) ≫
      (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusCompatibility.hom.app
        (DerivedCategory.Plus.Qh.obj M) =
    (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app M.obj := by
  change (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusιUnit.app M ≫ _ =
    (Sheaf.Γ X.smallEtaleTopology A).ιRightDerivedFunctorUnit.app M
  simp [Functor.rightDerivedFunctorPlusCompatibility]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem sectionsPullbackPlus_compatibility
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.whiskerRight (plusSectionsPullbackNat A f) DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft (upperStar A f).mapDerivedCategoryPlus
        (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorPlusCompatibility.hom =
    (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι (sectionsPullbackDerivedNat A f) := by
  let G := Sheaf.Γ Y.smallEtaleTopology A
  let H := Sheaf.Γ X.smallEtaleTopology A
  let L := upperStar A f
  apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusιUnit
    (HomotopyCategory.Plus.quasiIso _)
  ext M
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, plusSectionsPullbackNat_fac]
  rw [Functor.map_comp, Functor.map_comp]
  have hn := H.rightDerivedFunctorPlusCompatibility.hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  erw [Category.assoc, Category.assoc, hn]
  erw [reassoc_of% (sectionsCompatibility_fac A X (L.mapHomotopyCategoryPlus.obj M))]
  erw [reassoc_of% (sectionsCompatibility_fac A Y M)]
  erw [sectionsPullbackDerivedNat_fac A f M.obj]
  have hi : DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.inv.app M) =
      L.mapDerivedCategoryFactorsh.inv.app M.obj := by
    have hIso : DerivedCategory.Plus.ι.mapIso (L.mapDerivedCategoryPlusFactorsh.app M) =
        L.mapDerivedCategoryFactorsh.app M.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app L M)
    exact congrArg Iso.inv hIso
  change _ ≫ _ ≫ H.rightDerivedFunctor.map
    (DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.inv.app M)) = _
  rw [hi]
  congr 2

/-- Underlying abelian derived cohomology of a bounded-below module complex.
The comparison is the derived base-change map of the sectionwise scalar-forgetting
isomorphism, so its inverse is determined by its invertibility.
Source: Stacks Project, Tag 03FD.
(blueprint: lem-weil-pbc-derived-module-underlying-comparison). -/
noncomputable def moduleUnderlyingCohomologyIso (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) (n : ℤ) :
    (DerivedCategory.Plus.ι ⋙ cohomology (ModuleCat.{u + 1} Λ) X n) ⋙
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
    (moduleUnderlyingSheaf Λ X).mapDerivedCategoryPlus ⋙
      DerivedCategory.Plus.ι ⋙ cohomology AddCommGrpCat.{u + 1} X n := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let S := moduleUnderlyingSheaf Λ X
  let GM := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let GA := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let b := moduleUnderlyingGlobalSectionsIso Λ X
  refine Functor.isoWhiskerRight
    (Functor.isoWhiskerRight GM.rightDerivedFunctorPlusCompatibility.symm
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n)) U ≪≫ ?_
  refine Functor.isoWhiskerLeft GM.rightDerivedFunctorPlus
    (U.mapDerivedCategoryPlusHomologyFunctorIso n) ≪≫ ?_
  refine Functor.isoWhiskerRight b
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n) ≪≫ ?_
  exact Functor.isoWhiskerLeft S.mapDerivedCategoryPlus
    (Functor.isoWhiskerRight GA.rightDerivedFunctorPlusCompatibility
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem moduleUnderlyingCohomology_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
          ((sectionsPullbackDerivedNat (ModuleCat.{u + 1} Λ) f).app K.obj)) ≫
      (moduleUnderlyingCohomologyIso Λ X n).hom.app
        ((upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj K) ≫
      (DerivedCategory.Plus.ι ⋙ cohomology AddCommGrpCat.{u + 1} X n).map
        ((moduleUnderlyingPullbackDerivedIso Λ f).inv.app K) =
    (moduleUnderlyingCohomologyIso Λ Y n).hom.app K ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
        ((sectionsPullbackDerivedNat AddCommGrpCat.{u + 1} f).app
          (((moduleUnderlyingSheaf Λ Y).mapDerivedCategoryPlus.obj K).obj)) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let GM := Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let HM := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let GA := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let HA := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let LM := upperStar (ModuleCat.{u + 1} Λ) f
  let LA := upperStar AddCommGrpCat.{u + 1} f
  let SK := (moduleUnderlyingSheaf Λ Y).mapDerivedCategoryPlus.obj K
  let N := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n
  let M := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n
  have hM := congr_app (sectionsPullbackPlus_compatibility (ModuleCat.{u + 1} Λ) f) K
  have hA := congr_app (sectionsPullbackPlus_compatibility AddCommGrpCat.{u + 1} f) SK
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hM hA
  have hMi :
      (sectionsPullbackDerivedNat (ModuleCat.{u + 1} Λ) f).app K.obj ≫
        HM.rightDerivedFunctorPlusCompatibility.inv.app (LM.mapDerivedCategoryPlus.obj K) =
      GM.rightDerivedFunctorPlusCompatibility.inv.app K ≫
        DerivedCategory.Plus.ι.map ((plusSectionsPullbackNat (ModuleCat.{u + 1} Λ) f).app K) := by
    apply (cancel_epi (GM.rightDerivedFunctorPlusCompatibility.hom.app K)).mp
    erw [← Category.assoc, ← hM]
    erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    erw [Iso.hom_inv_id_app_assoc]
  have hd :
      DerivedCategory.Plus.ι.map
          (U.mapDerivedCategoryPlus.map
            ((plusSectionsPullbackNat (ModuleCat.{u + 1} Λ) f).app K)) ≫
        DerivedCategory.Plus.ι.map ((moduleUnderlyingGlobalSectionsIso Λ X).hom.app
          (LM.mapDerivedCategoryPlus.obj K)) ≫
        HA.rightDerivedFunctorPlusCompatibility.hom.app
          ((moduleUnderlyingSheaf Λ X).mapDerivedCategoryPlus.obj
            (LM.mapDerivedCategoryPlus.obj K)) ≫
        HA.rightDerivedFunctor.map (DerivedCategory.Plus.ι.map
          ((moduleUnderlyingPullbackDerivedIso Λ f).inv.app K)) =
      DerivedCategory.Plus.ι.map ((moduleUnderlyingGlobalSectionsIso Λ Y).hom.app K) ≫
        GA.rightDerivedFunctorPlusCompatibility.hom.app SK ≫
        (sectionsPullbackDerivedNat AddCommGrpCat.{u + 1} f).app SK.obj := by
    have hn := HA.rightDerivedFunctorPlusCompatibility.hom.naturality
      ((moduleUnderlyingPullbackDerivedIso Λ f).inv.app K)
    simp only [Functor.comp_map] at hn
    erw [← hn]
    have hs := congrArg (fun k ↦ DerivedCategory.Plus.ι.map k)
      (underlyingDerivedSections_naturality Λ f K)
    simp only [Functor.map_comp] at hs
    erw [reassoc_of% hs]
    exact congrArg (fun k ↦ DerivedCategory.Plus.ι.map
      ((moduleUnderlyingGlobalSectionsIso Λ Y).hom.app K) ≫ k) hA
  simp only [moduleUnderlyingCohomologyIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  rw [← U.map_comp_assoc, ← M.map_comp, hMi, M.map_comp, U.map_comp]
  have hn := (U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.naturality
    ((plusSectionsPullbackNat (ModuleCat.{u + 1} Λ) f).app K)
  simp only [Functor.comp_map] at hn
  erw [Category.assoc, reassoc_of% hn]
  simpa only [cohomology, rightDerivedGlobalSections, DerivedCategory.Plus.homologyFunctor,
    U, M, N, GM, HM, GA, HA, LM, SK, Functor.map_comp, Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ U.map (M.map (GM.rightDerivedFunctorPlusCompatibility.inv.app K)) ≫
      (U.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
        (GM.rightDerivedFunctorPlus.obj K) ≫ N.map k) hd


/-- Pullback and coefficient-forgetting comparisons for a bounded-below complex.
All data are constructed from the exact functor and the canonical adjunction mate.
Source: Stacks Project, Tags 03FD, 03D3 and 03D7.
(blueprint: lem-weil-pbc-derived-module-underlying-comparison). -/
noncomputable def moduleUnderlyingPullbackIso
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (X : Scheme.{u}) (p : X ⟶ T) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      ((cohomology (ModuleCat.{u + 1} Λ) X n).obj
        ((upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory.obj K.obj)) ≅
    (cohomology AddCommGrpCat.{u + 1} X n).obj
      ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.obj
        (((moduleUnderlyingSheaf Λ T).mapDerivedCategoryPlus.obj K).obj)) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let S := moduleUnderlyingSheaf Λ T
  let R := moduleUnderlyingSheaf Λ X
  let M := upperStar (ModuleCat.{u + 1} Λ) p
  let A := upperStar AddCommGrpCat.{u + 1} p
  let c := moduleUnderlyingPullbackDerivedIso Λ p
  exact (moduleUnderlyingCohomologyIso Λ X n).app (M.mapDerivedCategoryPlus.obj K) ≪≫
    (DerivedCategory.Plus.ι ⋙ cohomology AddCommGrpCat.{u + 1} X n).mapIso (c.app K).symm

/-- The constructed coefficient comparisons commute with canonical restriction.
This is a square for arbitrary composable scheme maps, with no inverse system,
limit, compactness, affine-transition, or continuity hypothesis or conclusion.

Source: Stacks Project, Tag 03FD (lemma-cohomology-modules-abelian-agree),
Tags 03D3 and 03D7, and Tag 01F8 (functoriality of restriction).
(blueprint: lem-weil-pbc-derived-module-underlying-comparison).

Proof: The sectionwise comparison used by `moduleUnderlyingCohomologyIso` is
natural for the adjunction unit. On a bounded-below injective module resolution,
its derived base-change map is the comparison from the underlying section complex
to the abelian derived section complex; injective module sheaves are section-acyclic
after forgetting scalars by Tag 03FD. The mate `upperStarForget₂` is characterized
by the underived unit equation `unit_comp_lowerStar_map_upperStarForget₂Comparison`.
Deriving this equation gives compatibility of the two restriction units.
The derived Leray comparisons satisfy the same equation by uniqueness of derived
comparison maps and compatibility with the units of right derivation.
For composable inverse images, mate composition identifies the two coefficient
comparison maps. Apply the exact-functor derived composition comparisons; their
localization factorization equations identify this with the composition factor
in `moduleDerivedRestriction` and `presentationDerivedMap`. Finally apply homology,
whose natural exact-forgetting comparison is part of `moduleUnderlyingCohomologyIso`.
The resulting square is exactly the equality below. Equivalently all factors may
be checked on resolutions: after precomposition with a pulled-back resolution,
the two maps into an abelian K-injective resolution agree; the comparison theorem
makes them equal up to homotopy, and homology identifies their induced maps. -/
theorem moduleUnderlyingPullbackIso_naturality
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (X Y : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T)
    (hh : h = f ≫ g) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (moduleDerivedRestriction Λ f g h hh K.obj n) ≫
      (moduleUnderlyingPullbackIso Λ T K n X h).hom =
    (moduleUnderlyingPullbackIso Λ T K n Y g).hom ≫
      presentationDerivedMap f g h hh
        (((moduleUnderlyingSheaf Λ T).mapDerivedCategoryPlus.obj K).obj) n := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let CM := underlyingPlusPullbackComp (ModuleCat.{u + 1} Λ) f g h hh
  let CA := underlyingPlusPullbackComp AddCommGrpCat.{u + 1} f g h hh
  let Mg := upperStar (ModuleCat.{u + 1} Λ) g
  let SK := (moduleUnderlyingSheaf Λ T).mapDerivedCategoryPlus.obj K
  let HX := cohomology AddCommGrpCat.{u + 1} X n
  let HY := cohomology AddCommGrpCat.{u + 1} Y n
  let MX := cohomology (ModuleCat.{u + 1} Λ) X n
  let M := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n
  let N := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n
  have hrM : moduleDerivedRestriction Λ f g h hh K.obj n =
      M.map ((sectionsPullbackDerivedNat (ModuleCat.{u + 1} Λ) f).app
        (Mg.mapDerivedCategoryPlus.obj K).obj) ≫
      MX.map (DerivedCategory.Plus.ι.map (CM.inv.app K)) := by
    rw [underlyingPlusPullbackComp_inv]
    simp only [moduleDerivedRestriction, sectionsPullbackDerivedNat, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, cohomology, Functor.comp_map, Functor.map_comp,
      Category.id_comp, Category.assoc]
    rfl
  have hrA : presentationDerivedMap f g h hh SK.obj n =
      N.map ((sectionsPullbackDerivedNat AddCommGrpCat.{u + 1} f).app
        ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlus.obj SK).obj) ≫
      HX.map (DerivedCategory.Plus.ι.map (CA.inv.app SK)) := by
    rw [underlyingPlusPullbackComp_inv]
    simp only [presentationDerivedMap, sectionsPullbackDerivedNat, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
      Functor.associator_hom_app, cohomology, Functor.comp_map, Functor.map_comp,
      Category.id_comp, Category.assoc]
    rfl
  have hc := underlyingPullbackDerived_composition Λ f g h hh K
  have hi := IsIso.inv_eq_inv.mpr hc
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at hi
  have hb := (moduleUnderlyingCohomologyIso Λ X n).hom.naturality (CM.inv.app K)
  simp only [Functor.comp_map] at hb
  have hs := moduleUnderlyingCohomology_restriction Λ f (Mg.mapDerivedCategoryPlus.obj K) n
  have hn := (sectionsPullbackDerivedNat AddCommGrpCat.{u + 1} f).naturality
    (DerivedCategory.Plus.ι.map ((moduleUnderlyingPullbackDerivedIso Λ g).inv.app K))
  simp only [Functor.comp_map] at hn
  have hnH := congrArg N.map hn
  simp only [Functor.map_comp] at hnH
  rw [hrM, hrA, U.map_comp]
  simp only [moduleUnderlyingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  erw [reassoc_of% hb]
  erw [← HX.map_comp, ← DerivedCategory.Plus.ι.map_comp, hi]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs]
  erw [← reassoc_of% hnH]
  rfl

end AlgebraicGeometry.Etale
