/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal

/-! # Supported-source normalization of the scalar/pullback mate

Source: diagonal coefficient changes, paragraph (3), supported source normalization.
(blueprint: lem-diagonal-supported-pullback-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedUpper derivedScalars singlePullback
  scalarPullbackComparison

private theorem exact_square_single (q : G ⋙ V ≅ U ⋙ F) (N : B) :
    F.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      ((Functor.mapDerivedCategoryCompIso G V).symm ≪≫
        Functor.mapDerivedCategoryNatIso q ≪≫
        Functor.mapDerivedCategoryCompIso U F).inv.app
          ((DerivedCategory.singleFunctor B 0).obj N) ≫
      V.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app N) =
    (F.mapDerivedCategorySingleFunctor 0).hom.app (U.obj N) ≫
      (DerivedCategory.singleFunctor C 0).map (q.inv.app N) ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app (G.obj N) := by
  apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app (G.obj N))).mp
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G V N]
  rw [show (Functor.mapDerivedCategoryNatIso q).inv =
    (Functor.mapDerivedCategoryNatIso q.symm).hom from rfl]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor q.symm N]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U F N]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [F.mapDerivedCategory.map_id, Category.id_comp]
  simp only [Iso.symm_hom]
  erw [Category.comp_id]

private theorem exact_square_single_transport
    (LF : DerivedCategory A ⥤ DerivedCategory C)
    (LG : DerivedCategory B ⥤ DerivedCategory D)
    (iF : LF ≅ F.mapDerivedCategory) (iG : LG ≅ G.mapDerivedCategory)
    (q : G ⋙ V ≅ U ⋙ F) (N : B) :
    LF.map ((U.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (Functor.isoWhiskerRight iG V.mapDerivedCategory ≪≫
        (Functor.mapDerivedCategoryCompIso G V).symm ≪≫
        Functor.mapDerivedCategoryNatIso q ≪≫
        Functor.mapDerivedCategoryCompIso U F ≪≫
        Functor.isoWhiskerLeft U.mapDerivedCategory iF.symm).inv.app
          ((DerivedCategory.singleFunctor B 0).obj N) ≫
      V.mapDerivedCategory.map (iG.hom.app _ ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app N) =
    iF.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app (U.obj N) ≫
      (DerivedCategory.singleFunctor C 0).map (q.inv.app N) ≫
        (V.mapDerivedCategorySingleFunctor 0).inv.app (G.obj N) := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% iF.hom.naturality
    ((U.mapDerivedCategorySingleFunctor 0).inv.app N)]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have h := exact_square_single F G U V q N
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc] at h
  rw [h]

private theorem scalar_mate_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {T : A ⥤ B} {U : B ⥤ A} {S : C ⥤ D} {V : D ⥤ C}
    (a : T ⊣ U) (b : S ⊣ V) (F : A ⥤ C) (G : B ⥤ D)
    (e : G ⋙ V ≅ U ⋙ F)
    {M : A} {M' : B} {P : C} {P' : D}
    (c : T.obj M ⟶ M') (d : S.obj P ⟶ P')
    (p : F.obj M ⟶ P) (q : G.obj M' ⟶ P')
    (h : F.map (a.homEquiv _ _ c) ≫ e.inv.app M' ≫ V.map q =
      p ≫ b.homEquiv _ _ d) :
    (Adjunction.pushHomOfComapIso a b e).app M ≫ G.map c ≫ q = S.map p ≫ d := by
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ e.inv) M
  change F.map (a.unit.app M) ≫ e.inv.app (T.obj M) =
    b.unit.app (F.obj M) ≫
      V.map ((Adjunction.pushHomOfComapIso a b e).app M) at hm
  rw [← reassoc_of% hm]
  have hn := e.inv.naturality c
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← F.map_comp_assoc]
  have hp := b.unit.naturality p
  dsimp only [Functor.id_map, Functor.comp_map] at hp
  rw [← reassoc_of% hp]
  simpa only [Adjunction.homEquiv_unit] using h

private theorem restriction_pullback_single
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (N : Modules T S) :
    (derivedUpper R f).map
        (((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      (scalarRestrictionPullbackIso a f).inv.app
        ((DerivedCategory.singleFunctor (Modules T S) 0).obj N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        ((singlePullback T f N).hom) =
    (singlePullback R f ((Mod.comap (coefficientMap a S)).obj N)).hom ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map
        ((CondensedRing.comapUpperStarIso a f).inv.app N) ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app
        ((CondensedRing.upperStar T f).obj N) := by
  simpa only [scalarRestrictionPullbackIso, singlePullback, derivedUpper,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.app_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    CondensedRing.derivedComapUpperStarIso, Iso.trans_assoc, Category.assoc] using
    exact_square_single_transport (CondensedRing.upperStar R f)
      (CondensedRing.upperStar T f) (Mod.comap (coefficientMap a S))
      (Mod.comap (coefficientMap a X)) _ _
      (CondensedRing.upperStar R f).leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar T f).leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.comapUpperStarIso a f) N

private theorem single_pullback_naturality
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} (f : X ⟶ S) {M N : Modules R S} (v : M ⟶ N) :
    (derivedUpper R f).map ((DerivedCategory.singleFunctor (Modules R S) 0).map v) ≫
        (singlePullback R f N).hom =
      (singlePullback R f M).hom ≫
        (DerivedCategory.singleFunctor (Modules R X) 0).map
          ((CondensedRing.upperStar R f).map v) := by
  simpa only [singlePullback, derivedUpper, Functor.comp_map, Iso.app_hom] using
    (Functor.singleFunctorCompLeftDerivedFunctorIso (CondensedRing.upperStar R f)).hom.naturality v

private theorem scalar_mate_single
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules R S) (N : Modules T S) (M' : Modules R X) (N' : Modules T X)
    (v : M ⟶ (Mod.comap (coefficientMap a S)).obj N)
    (w : M' ⟶ (Mod.comap (coefficientMap a X)).obj N')
    (p : (CondensedRing.upperStar R f).obj M ⟶ M')
    (q : (CondensedRing.upperStar T f).obj N ⟶ N')
    (c : (derivedScalars a S).obj
      ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules T S) 0).obj N)
    (d : (derivedScalars a X).obj
      ((DerivedCategory.singleFunctor (Modules R X) 0).obj M') ⟶
      (DerivedCategory.singleFunctor (Modules T X) 0).obj N')
    (hc : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a S)).homEquiv _ _ c =
      (DerivedCategory.singleFunctor (Modules R S) 0).map v ≫
      ((Mod.comap (coefficientMap a S)).mapDerivedCategorySingleFunctor 0).inv.app N)
    (hd : (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a X)).homEquiv _ _ d =
      (DerivedCategory.singleFunctor (Modules R X) 0).map w ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N')
    (hp : (CondensedRing.upperStar R f).map v ≫
      (CondensedRing.comapUpperStarIso a f).inv.app N ≫
      (Mod.comap (coefficientMap a X)).map q = p ≫ w) :
    (scalarPullbackComparison a f).app
        ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ≫
      (derivedUpper T f).map c ≫ (singlePullback T f N).hom ≫
      (DerivedCategory.singleFunctor (Modules T X) 0).map q =
    (derivedScalars a X).map ((singlePullback R f M).hom ≫
      (DerivedCategory.singleFunctor (Modules R X) 0).map p) ≫ d := by
  refine scalar_mate_endpoint
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (derivedUpper R f) (derivedUpper T f) (scalarRestrictionPullbackIso a f) c d
    ((singlePullback R f M).hom ≫ (DerivedCategory.singleFunctor (Modules R X) 0).map p)
    ((singlePullback T f N).hom ≫ (DerivedCategory.singleFunctor (Modules T X) 0).map q) ?_
  rw [hc, hd]
  simp only [Functor.map_comp, Category.assoc]
  have hn := ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor
    0).inv.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% restriction_pullback_single a f N]
  rw [reassoc_of% single_pullback_naturality]
  rw [← hn]
  have hh := congrArg (fun z ↦ (DerivedCategory.singleFunctor (Modules R X) 0).map z) hp
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh]

private theorem pull_congr_compatible
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} {f g : X ⟶ S} (e : f = g) :
    NatTrans.SquareCompatible (CondensedRing.comapUpperStarIso a f)
      (CondensedRing.comapUpperStarIso a g)
      (CondensedRing.upperStarCongr T e).hom (CondensedRing.upperStarCongr R e).hom := by
  cases e
  simpa only [CondensedRing.upperStarCongr_self, Iso.refl_hom] using
    NatTrans.SquareCompatible.id (CondensedRing.comapUpperStarIso a f)

private theorem scalar_pullback_square_compatible
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (CondensedRing.comapUpperStarIso a hS)
        (CondensedRing.comapUpperStarIso a f'))
      (Functor.pasteSquareIso (CondensedRing.comapUpperStarIso a f)
        (CondensedRing.comapUpperStarIso a hX))
      (((CondensedRing.upperStarComp T f' hS).symm ≪≫
        CondensedRing.upperStarCongr T h ≪≫ CondensedRing.upperStarComp T hX f).hom)
      (((CondensedRing.upperStarComp R f' hS).symm ≪≫
        CondensedRing.upperStarCongr R h ≪≫ CondensedRing.upperStarComp R hX f).hom) := by
  have hc := ((CondensedRing.squareCompatible_upperStarComp a f' hS).inv.comp
    (pull_congr_compatible a h)).comp (CondensedRing.squareCompatible_upperStarComp a hX f)
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hc

private theorem scalar_exchange_compatible
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (CondensedRing.comapLowerStarIso a f)
        (CondensedRing.comapUpperStarIso a hS))
      (Functor.pasteSquareIso (CondensedRing.comapUpperStarIso a hX)
        (CondensedRing.comapLowerStarIso a f'))
      (ordinaryExchange T f f' hX hS h) (ordinaryExchange R f f' hX hS h) := by
  simpa only [ordinaryExchange] using
    NatTrans.SquareCompatible.exchangeRight
      (CondensedRing.isMateSquare_comapUpperStarIso_comapLowerStarIso a f)
      (CondensedRing.isMateSquare_comapUpperStarIso_comapLowerStarIso a f')
      (scalar_pullback_square_compatible a f f' hX hS h)

private theorem square_compatible_inv_app
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {T : A ⥤ A'} {T' : B ⥤ B'} {F G : A ⥤ B} {F' G' : A' ⥤ B'}
    {iF : F ⋙ T' ≅ T ⋙ F'} {iG : G ⋙ T' ≅ T ⋙ G'}
    {a : F ⟶ G} {b : F' ⟶ G'}
    (h : NatTrans.SquareCompatible iF iG a b) (M : A) :
    iF.inv.app M ≫ T'.map (a.app M) = b.app (T.obj M) ≫ iG.inv.app M := by
  apply (cancel_mono (iG.hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h M, Iso.inv_hom_id_app_assoc]
  exact (Category.comp_id (b.app (T.obj M))).symm

private theorem pasted_square_compatible_inv_app
    {A B B₂ C A' B' B₂' C' : Type*}
    [Category A] [Category B] [Category B₂] [Category C]
    [Category A'] [Category B'] [Category B₂'] [Category C']
    {TA : A ⥤ A'} {TB : B ⥤ B'} {TB₂ : B₂ ⥤ B₂'} {TC : C ⥤ C'}
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ B₂} {I : B₂ ⥤ C}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ B₂'} {I' : B₂' ⥤ C'}
    (iF : F ⋙ TB ≅ TA ⋙ F') (iG : G ⋙ TC ≅ TB ⋙ G')
    (iH : H ⋙ TB₂ ≅ TA ⋙ H') (iI : I ⋙ TC ≅ TB₂ ⋙ I')
    {a : F ⋙ G ⟶ H ⋙ I} {b : F' ⋙ G' ⟶ H' ⋙ I'}
    (h : NatTrans.SquareCompatible (Functor.pasteSquareIso iF iG)
      (Functor.pasteSquareIso iH iI) a b) (M : A) :
    G'.map (iF.inv.app M) ≫ iG.inv.app (F.obj M) ≫ TC.map (a.app M) =
      b.app (TA.obj M) ≫ I'.map (iH.inv.app M) ≫ iI.inv.app (H.obj M) := by
  simpa only [Functor.pasteSquareIso_inv_app, Category.assoc] using
    square_compatible_inv_app h M

private theorem supported_square_of_compatible
    {A B B₂ C A' B' B₂' C' : Type*}
    [Category A] [Category B] [Category B₂] [Category C]
    [Category A'] [Category B'] [Category B₂'] [Category C']
    {TA : A ⥤ A'} {TB : B ⥤ B'} {TB₂ : B₂ ⥤ B₂'} {TC : C ⥤ C'}
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ B₂} {I : B₂ ⥤ C}
    {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ B₂'} {I' : B₂' ⥤ C'}
    (iF : F ⋙ TB ≅ TA ⋙ F') (iG : G ⋙ TC ≅ TB ⋙ G')
    (iH : H ⋙ TB₂ ≅ TA ⋙ H') (iI : I ⋙ TC ≅ TB₂ ⋙ I')
    {a : F ⋙ G ⟶ H ⋙ I} {b : F' ⋙ G' ⟶ H' ⋙ I'}
    (h : NatTrans.SquareCompatible (Functor.pasteSquareIso iF iG)
      (Functor.pasteSquareIso iH iI) a b)
    (M₀ : A') (M : A) (N₀ : B₂') (N : B₂)
    (v : M₀ ⟶ TA.obj M) (w : N₀ ⟶ TB₂.obj N)
    (p₀ : H'.obj M₀ ⟶ N₀) (p : H.obj M ⟶ N)
    (hp : H'.map v ≫ iH.inv.app M ≫ TB₂.map p = p₀ ≫ w) :
    G'.map (F'.map v ≫ iF.inv.app M) ≫ iG.inv.app (F.obj M) ≫
        TC.map (a.app M ≫ I.map p) =
      (b.app M₀ ≫ I'.map p₀) ≫ (I'.map w ≫ iI.inv.app N) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (pasted_square_compatible_inv_app iF iG iH iI h M)]
  have he := b.naturality v
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  have hn := iI.inv.naturality p
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  have hh := congrArg I'.map hp
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh]

private theorem native_supported_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (M₀ : Modules R X) (M : Modules T X) (N₀ : Modules R X') (N : Modules T X')
    (v : M₀ ⟶ (Mod.comap (coefficientMap a X)).obj M)
    (w : N₀ ⟶ (Mod.comap (coefficientMap a X')).obj N)
    (p₀ : (CondensedRing.upperStar R hX).obj M₀ ⟶ N₀)
    (p : (CondensedRing.upperStar T hX).obj M ⟶ N)
    (hp : (CondensedRing.upperStar R hX).map v ≫
      (CondensedRing.comapUpperStarIso a hX).inv.app M ≫
      (Mod.comap (coefficientMap a X')).map p = p₀ ≫ w) :
    (CondensedRing.upperStar R hS).map
        ((CondensedRing.lowerStar R f).map v ≫
          (CondensedRing.comapLowerStarIso a f).inv.app M) ≫
      (CondensedRing.comapUpperStarIso a hS).inv.app
        ((CondensedRing.lowerStar T f).obj M) ≫
      (Mod.comap (coefficientMap a S')).map
        ((ordinaryExchange T f f' hX hS h).app M ≫
          (CondensedRing.lowerStar T f').map p) =
    ((ordinaryExchange R f f' hX hS h).app M₀ ≫
      (CondensedRing.lowerStar R f').map p₀) ≫
      ((CondensedRing.lowerStar R f').map w ≫
        (CondensedRing.comapLowerStarIso a f').inv.app N) := by
  exact supported_square_of_compatible
    (CondensedRing.comapLowerStarIso a f) (CondensedRing.comapUpperStarIso a hS)
    (CondensedRing.comapUpperStarIso a hX) (CondensedRing.comapLowerStarIso a f')
    (scalar_exchange_compatible a f f' hX hS h) M₀ M N₀ N v w p₀ p hp

private theorem pull_endpoint_underlying
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules R S) (N : Modules R X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X) (p : PullEndpoint R f M N m) :
    CondensedRing.upperStarUnitHom R f M ≫ p.iso.hom.hom = m := by
  apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  rw [← p.normalization, CondensedRing.upperStarLowerStarAdjunction_homEquiv_hom]
  rfl

private theorem scalar_square_from_unit
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules R S) (N : Modules T S) (M' : Modules R X) (N' : Modules T X)
    (v : M ⟶ (Mod.comap (coefficientMap a S)).obj N)
    (w : M' ⟶ (Mod.comap (coefficientMap a X)).obj N')
    (p : (CondensedRing.upperStar R f).obj M ⟶ M')
    (q : (CondensedRing.upperStar T f).obj N ⟶ N')
    (h : (upperStar Ab.{u + 1} f).map v.hom ≫
        (CondensedRing.upperStarUnitHom T f N ≫ q.hom) =
      (CondensedRing.upperStarUnitHom R f M ≫ p.hom) ≫ w.hom) :
    (CondensedRing.upperStar R f).map v ≫
        (CondensedRing.comapUpperStarIso a f).inv.app N ≫
        (Mod.comap (coefficientMap a X)).map q = p ≫ w := by
  apply Mod.hom_ext_of_extendUnitHom (condensedPullbackHom R f)
  change CondensedRing.upperStarUnitHom R f M ≫ _ =
    CondensedRing.upperStarUnitHom R f M ≫ _
  simp only [Mod.comp_hom', Mod.comap_map_hom]
  rw [CondensedRing.upperStarUnitHom_map_hom_assoc,
    CondensedRing.upperStarUnitHom_comapUpperStarIso_inv_app_hom_assoc]
  simpa only [Category.assoc] using h

private theorem normalized_pullback_scalar_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (M₀ : Modules R S) (M : Modules T S) (N₀ : Modules R X) (N : Modules T X)
    (m₀ : (upperStar Ab.{u + 1} f).obj M₀.X ⟶ N₀.X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (p₀ : PullEndpoint R f M₀ N₀ m₀) (p : PullEndpoint T f M N m)
    (v : M₀ ⟶ (Mod.comap (coefficientMap a S)).obj M)
    (w : N₀ ⟶ (Mod.comap (coefficientMap a X)).obj N)
    (hvw : (upperStar Ab.{u + 1} f).map v.hom ≫ m = m₀ ≫ w.hom) :
    (CondensedRing.upperStar R f).map v ≫
        (CondensedRing.comapUpperStarIso a f).inv.app M ≫
        (Mod.comap (coefficientMap a X)).map p.iso.hom = p₀.iso.hom ≫ w := by
  apply scalar_square_from_unit a f M₀ M N₀ N v w p₀.iso.hom p.iso.hom
  rw [pull_endpoint_underlying R f M₀ N₀ m₀ p₀,
    pull_endpoint_underlying T f M N m p]
  exact hvw

private theorem coefficient_endpoint_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X X' : Scheme.{u}} (f : X' ⟶ X)
    (c : Endpoint a (Mod.regular (condensedRingObj R X))
      (Mod.regular (condensedRingObj T X)) (coefficientMap a X))
    (c' : Endpoint a (Mod.regular (condensedRingObj R X'))
      (Mod.regular (condensedRingObj T X')) (coefficientMap a X')) :
    (upperStar Ab.{u + 1} f).map c.semilinear.hom.hom ≫ condensedPullbackHom T f =
      condensedPullbackHom R f ≫ c'.semilinear.hom.hom := by
  rw [c.semilinear.underlying, c'.semilinear.underlying]
  exact map_coefficientMap_comp_condensedPullbackHom a f

/-- Supported coefficient endpoints commute with geometric inverse image under the
scalar mate. The coefficient change is arbitrary; no positive line or diagonal class
occurs in the equation, and no diagram or trace compatibility is assumed.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), closed diagonal base change;
lem-diagonal-quotient-class-pullback, proof step 1 (supported-source part).
(blueprint: lem-diagonal-supported-pullback-scalar-normalization).

Proof: Transpose the displayed composites through the scalar adjunction at the primed
surface. Replace the scalar endpoint maps by their normalized degree-zero semilinear
maps and use the exact inverse-image single comparison. SourcePullback's supported
normalization replaces each geometric supported map by sourcePullbackMap, the ordinary
exchange followed by the coefficient-unit map. The definition of supportMap replaces
each scalar supported map by direct image of its unit semilinear map followed by the
restriction/direct-image comparison. These ordinary maps commute: transpose once more
through the diagonal adjunction, expand the ordinary exchange mate, and use naturality
of the coefficient unit together with the unit/counit triangle identities. Both orders
are the same coefficient map on the primed projective line, followed by the same
diagonal counit. Unit Endpoint and PullEndpoint normalization fixes the unit maps, so
there is no rescaling. Faithfulness of the module forgetful functor identifies the
ordinary module arrows. Apply the degree-zero functor and injectivity of the scalar
adjunction to recover the displayed equality. No flatness of a, or noetherian hypothesis,
is required: the supplied endpoints already assert the relevant isomorphisms. -/
theorem diagonalSupported_pullbackScalarNormalization
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L₀ : ∀ X : Scheme.{u}, Modules R X) (L : ∀ X : Scheme.{u}, Modules T X)
    (m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X)
    (m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (s₀ : SourcePullback R g L₀ m₀P m₀W) (s : SourcePullback T g L mP mW)
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (c' : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      (coefficientMap a (ProjectiveLine Y')))
    (e : Endpoint a (source R Y) (source T Y) (supportMap a Y c.semilinear.hom).hom)
    (e' : Endpoint a (source R Y') (source T Y') (supportMap a Y' c'.semilinear.hom).hom) :
    (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map e.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          s₀.supported.hom) ≫ e'.iso.hom := by
  have he : e.semilinear.hom = supportMap a Y c.semilinear.hom := by
    apply Mod.hom_ext
    exact e.semilinear.underlying
  have he' : e'.semilinear.hom = supportMap a Y' c'.semilinear.hom := by
    apply Mod.hom_ext
    exact e'.semilinear.underlying
  have hs :=
    native_supported_square (X := ProjectiveLine Y) (S := diagonalSurface Y)
      (X' := ProjectiveLine Y') (S' := diagonalSurface Y')
      a (diagonalImmersion Y) (diagonalImmersion Y') (baseP g) (baseW g) s.geometry.diagonal_square
      (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      c.semilinear.hom c'.semilinear.hom s₀.endpoints.cP.iso.hom s.endpoints.cP.iso.hom
      (normalized_pullback_scalar_square a (baseP g)
        (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
        (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
        (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
        (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
        (condensedPullbackHom R (baseP g)) (condensedPullbackHom T (baseP g))
        s₀.endpoints.cP s.endpoints.cP c.semilinear.hom c'.semilinear.hom
        (coefficient_endpoint_square a (baseP g) c c'))
  have ho :
      (CondensedRing.upperStar R (baseW g)).map e.semilinear.hom ≫
        (CondensedRing.comapUpperStarIso a (baseW g)).inv.app (source T Y) ≫
          (Mod.comap (coefficientMap a (diagonalSurface Y'))).map s.supported.hom =
        s₀.supported.hom ≫ e'.semilinear.hom := by
    rw [he, he', s.supported_normalization, s₀.supported_normalization]
    supported_native_exact hs
  supported_native_exact (scalar_mate_single (a := a) (f := baseW g)
    (M := source R Y) (N := source T Y) (M' := source R Y') (N' := source T Y')
    (v := e.semilinear.hom) (w := e'.semilinear.hom)
    (p := s₀.supported.hom) (q := s.supported.hom)
    (c := e.iso.hom) (d := e'.iso.hom) e.normalization e'.normalization ho)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
