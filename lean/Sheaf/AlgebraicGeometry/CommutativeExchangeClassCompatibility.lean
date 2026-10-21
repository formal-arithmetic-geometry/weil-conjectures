/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CommutativeExchangeRawPullback
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility

/-! # Compatibility of the exchange mate with raw classes -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option autoImplicit false
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Functor.mapDerivedCategoryPlus Functor.rightDerivedFunctorPlus

private theorem free_pullback_naturality {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
    (B : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : ((g)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree S).obj U) ⟶ B) :
    (abelianFreeRepresentablePullbackIso g U).inv ≫ s =
      (freeRepresentableHomEquiv T (g.Etale.obj U) B).symm
        (freeRepresentableHomEquiv S U (((g)_*[AddCommGrpCat.{u + 1}]).obj B)
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _ s)) := by
  let e (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ F).trans
      ((freeRepresentableHomEquiv S U (((g)_*[AddCommGrpCat.{u + 1}]).obj F)).trans
        (freeRepresentableHomEquiv T (g.Etale.obj U) F).symm)
  have he {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (x : ((g)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree S).obj U) ⟶ F)
      (b : F ⟶ G) : e G (x ≫ b) = e F x ≫ b := by
    apply (freeRepresentableHomEquiv T (g.Etale.obj U) G).injective
    simp only [e, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right, freeRepresentableHomEquiv_comp]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  change e _ (𝟙 _) ≫ s = e B s
  simpa only [Category.id_comp] using (he (𝟙 _) s).symm

private theorem free_hom_evaluation {S : Scheme.{u}} (U : S.Etale)
    (H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : (abelianComparisonFree S).obj U ⟶ H) :
    freeRepresentableHomEquiv S U H v = v.hom.app (op U)
      ((toSheafify S.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)
          (FreeAbelianGroup.of (ULift.up (𝟙 U)))) := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private noncomputable abbrev higherClassMorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    (abelianComparisonFree Y).obj U ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
    (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.homEquiv _ _
        ((((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((abelianComparisonFree Y).obj U) ≫ z)) ≫ (abelianComparisonShift f q F).hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem higher_class_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    abelianHigherDirectImageClass f q F U z =
      freeRepresentableHomEquiv Y U
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          (R+((f)_*[AddCommGrpCat.{u + 1}]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
        (higherClassMorphism f F q U z) := by
  exact (free_hom_evaluation U _ (higherClassMorphism f F q U z)).symm

private theorem free_pullback_sections {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
    (B : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H₀ : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : (abelianComparisonFree S).obj U ⟶ H₀)
    (E : ((g)^*[AddCommGrpCat.{u + 1}]).obj H₀ ⟶ B) :
    freeRepresentableHomEquiv T (g.Etale.obj U) B
        ((abelianFreeRepresentablePullbackIso g U).inv ≫
          ((g)^*[AddCommGrpCat.{u + 1}]).map v ≫ E) =
      E.hom.app (op (g.Etale.obj U))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H₀).hom.app
          (op U) (freeRepresentableHomEquiv S U H₀ v)) := by
  have he := free_pullback_naturality g U B
    (((g)^*[AddCommGrpCat.{u + 1}]).map v ≫ E)
  have h := congrArg (freeRepresentableHomEquiv T (g.Etale.obj U) B) he
  rw [Equiv.apply_symm_apply] at h
  have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality v
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hm : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _
        (((g)^*[AddCommGrpCat.{u + 1}]).map v ≫ E) =
      v ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H₀ ≫
        ((g)_*[AddCommGrpCat.{u + 1}]).map E := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu]
    exact Category.assoc _ _ _
  have hv : freeRepresentableHomEquiv S U (((g)_*[AddCommGrpCat.{u + 1}]).obj B)
        (v ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H₀ ≫
          ((g)_*[AddCommGrpCat.{u + 1}]).map E) =
      E.hom.app (op (g.Etale.obj U))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H₀).hom.app
          (op U) (freeRepresentableHomEquiv S U H₀ v)) := by
    rw [freeRepresentableHomEquiv_comp]
    rfl
  exact h.trans ((congrArg
    (freeRepresentableHomEquiv S U (((g)_*[AddCommGrpCat.{u + 1}]).obj B)) hm).trans hv)

private theorem class_sections_transport {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
    (H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : (abelianComparisonFree S).obj U ⟶ H)
    (v' : (abelianComparisonFree T).obj (g.Etale.obj U) ⟶ H')
    (E : ((g)^*[AddCommGrpCat.{u + 1}]).obj H ⟶ H')
    (hv : (abelianFreeRepresentablePullbackIso g U).inv ≫
      ((g)^*[AddCommGrpCat.{u + 1}]).map v ≫ E = v')
    (x : H.obj.obj (op U)) (x' : H'.obj.obj (op (g.Etale.obj U)))
    (hx : x = freeRepresentableHomEquiv S U H v)
    (hx' : x' = freeRepresentableHomEquiv T (g.Etale.obj U) H' v') :
    E.hom.app (op (g.Etale.obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H).hom.app
        (op U) x) = x' := by
  rw [hx, hx']
  exact (free_pullback_sections g U H' H v E).symm.trans
    (congrArg (freeRepresentableHomEquiv T (g.Etale.obj U) H') hv)

private theorem exact_homology_class
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (A : C) (K : DerivedCategory.Plus C) (K' : DerivedCategory.Plus D) (q : ℕ)
    (h : (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶ K⟦(q : ℤ)⟧)
    (t : G.mapDerivedCategoryPlus.obj K ⟶ K') :
    G.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctor C 0).map h ≫
        ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso
          (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K) ≫
      (G.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom.app K ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map t =
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj A) ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        ((G.mapDerivedCategoryPlusSingleFunctor 0).inv.app A ≫
          G.mapDerivedCategoryPlus.map h ≫
          (G.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app K ≫
          (shiftFunctor _ (q : ℤ)).map t) ≫
      ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K' := by
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let H₀' := DerivedCategory.Plus.homologyFunctor D 0
  let ν := G.mapDerivedCategoryPlusHomologyFunctorIso 0
  let c := G.mapDerivedCategoryPlusSingleFunctor 0
  let s := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 0
  let s' := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D) 0
  have hsingle : G.map (s.inv.app A) ≫ ν.hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj A) =
      s'.inv.app (G.obj A) ≫ H₀'.map (c.inv.app A) := by
    apply (cancel_mono (H₀'.map (c.hom.app A) ≫ s'.hom.app (G.obj A))).1
    have hc := G.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_singleFunctor 0 A
    change ν.hom.app _ ≫ H₀'.map (c.hom.app A) ≫ s'.hom.app _ =
      G.map (s.hom.app A) at hc
    simp only [Category.assoc]
    rw [hc]
    simp only [← G.map_comp, Iso.inv_hom_id_app, ← H₀'.map_comp_assoc]
    erw [G.map_id, H₀'.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_app]
    rfl
  have hn := ν.hom.naturality h
  simp only [Functor.comp_map] at hn
  have hs := G.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_shiftIso
    (q : ℤ) 0 (q : ℤ) (add_zero _) K
  have ht := ((H₀'.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).hom).naturality t
  simp only [Functor.comp_map] at ht
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hn, reassoc_of% hsingle]
  erw [← ht]
  rfl

private theorem homology_class_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (A : C) (A' : D) (e : A' ⟶ P.obj A)
    (K : DerivedCategory.Plus C) (K' : DerivedCategory.Plus D) (q : ℕ)
    (h : (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶ K⟦(q : ℤ)⟧)
    (h' : (DerivedCategory.Plus.singleFunctor D 0).obj A' ⟶ K'⟦(q : ℤ)⟧)
    (t : P.mapDerivedCategoryPlus.obj K ⟶ K')
    (hh : (DerivedCategory.Plus.singleFunctor D 0).map e ≫
        (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app A ≫
        P.mapDerivedCategoryPlus.map h ≫
        (P.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app K ≫
        (shiftFunctor _ (q : ℤ)).map t = h') :
    e ≫ P.map
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
          (DerivedCategory.Plus.homologyFunctor C 0).map h ≫
          ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K) ≫
      (P.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom.app K ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map t =
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A' ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map h' ≫
      ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K' := by
  have hg := exact_homology_class P A K K' q h t
  have hf := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.naturality e
  simp only [Functor.id_map, Functor.comp_map] at hf
  rw [hg, ← Category.assoc e, hf]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [hh]

private theorem mate_homology_class
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (L' : E ⥤ F) (P : C ⥤ E) (Q : D ⥤ F)
    [L.Additive] [L'.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus C)
    (R' : DerivedCategory.Plus F ⥤ DerivedCategory.Plus E)
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L.mapDerivedCategoryPlus ⊣ R) (adj' : L'.mapDerivedCategoryPlus ⊣ R')
    (θ : TwoSquare P.mapDerivedCategoryPlus L.mapDerivedCategoryPlus
      L'.mapDerivedCategoryPlus Q.mapDerivedCategoryPlus)
    (β : R ⋙ P.mapDerivedCategoryPlus ⟶ Q.mapDerivedCategoryPlus ⋙ R')
    (hβ : (mateEquiv adj adj' θ).natTrans = β) [NatTrans.CommShift β ℤ]
    (A : C) (A' : E) (e : A' ⟶ P.obj A)
    (K : DerivedCategory.Plus D) (K' : DerivedCategory.Plus F) (q : ℕ)
    (z : L.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A) ⟶
      K⟦(q : ℤ)⟧)
    (z' : L'.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor E 0).obj A') ⟶
      K'⟦(q : ℤ)⟧)
    (c : Q.mapDerivedCategoryPlus.obj K ⟶ K')
    (hz : L'.mapDerivedCategoryPlus.map
        ((DerivedCategory.Plus.singleFunctor E 0).map e ≫
          (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app A) ≫
      θ.natTrans.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≫
      Q.mapDerivedCategoryPlus.map z ≫
      (Q.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app K ≫
      (shiftFunctor _ (q : ℤ)).map c = z') :
    e ≫ P.map
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
          (DerivedCategory.Plus.homologyFunctor C 0).map (adj.homEquiv _ _ z) ≫
          ((DerivedCategory.Plus.homologyFunctor C 0).mapIso
            ((R.commShiftIso (q : ℤ)).app K) ≪≫
            ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso
              (q : ℤ) 0 (q : ℤ) (add_zero _)).app (R.obj K)).hom) ≫
      (P.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom.app (R.obj K) ≫
      (DerivedCategory.Plus.homologyFunctor E (q : ℤ)).map (β.app K ≫ R'.map c) =
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A' ≫
      (DerivedCategory.Plus.homologyFunctor E 0).map (adj'.homEquiv _ _ z') ≫
      ((DerivedCategory.Plus.homologyFunctor E 0).mapIso
        ((R'.commShiftIso (q : ℤ)).app K') ≪≫
        ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso
          (q : ℤ) 0 (q : ℤ) (add_zero _)).app (R'.obj K')).hom := by
  let : NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ := by
    rw [hβ]
    infer_instance
  have hm := shifted_adjunct_mate_transport adj adj' P.mapDerivedCategoryPlus
    Q.mapDerivedCategoryPlus θ (q : ℤ)
    ((DerivedCategory.Plus.singleFunctor E 0).map e ≫
      (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app A) z c
  rw [hβ, hz] at hm
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc] using
    homology_class_transport P A A' e (R.obj K) (R'.obj K') q
    (adj.homEquiv _ _ z ≫ (R.commShiftIso (q : ℤ)).hom.app K)
    (adj'.homEquiv _ _ z' ≫ (R'.commShiftIso (q : ℤ)).hom.app K')
    (β.app K ≫ R'.map c) (by simpa only [Category.assoc] using hm)

private theorem square_single_comparison
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    D+((f')^*[AddCommGrpCat.{u + 1}]).map
        ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app A) ≫
      (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫
      D+((g')^*[AddCommGrpCat.{u + 1}]).map
        ((((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A) =
    (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app A) ≫
      (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ := by
  apply (cancel_mono
    ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _)).1
  rw [pullbackSquareComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% (comp_single_inv AddCommGrpCat.{u + 1} f' g (g' ≫ f) sq.w A)]
  rw [comp_single AddCommGrpCat.{u + 1} g' f (g' ≫ f) rfl A]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    squareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp]
  erw [Category.comp_id]

private theorem raw_pullback_source
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (A' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ((g)^*[AddCommGrpCat.{u + 1}]).obj A ≅ A')
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj A) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    D+((f')^*[AddCommGrpCat.{u + 1}]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
          (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app A) ≫
      (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫
      D+((g')^*[AddCommGrpCat.{u + 1}]).map
        ((((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ z) ≫
      (D+((g')^*[AddCommGrpCat.{u + 1}]).commShiftIso (q : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (shiftFunctor _ (q : ℤ)).map
        ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) =
    (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A' ≫
      commutativeExchangeTransport ((g')^*[AddCommGrpCat.{u + 1}]) q
        (((squareUpperStarIso AddCommGrpCat.{u + 1} sq).symm.app A) ≪≫
          ((f')^*[AddCommGrpCat.{u + 1}]).mapIso e) z := by
  rw [commutativeExchangeTransport_def]
  have hs := square_single_comparison sq A
  have he :=
    (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality e.inv
  simp only [Functor.comp_map] at he
  dsimp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs, reassoc_of% he]

set_option backward.isDefEq.respectTransparency true in
private theorem derived_exchange_mate (B : Type (u + 2)) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    (mateEquiv
      (upperStarLowerStarAdjunction B f).derivedPlus
      (upperStarLowerStarAdjunction B f').derivedPlus
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom)).natTrans =
      derivedBaseChangeMapPlus B sq := by
  exact derivedBaseChangeMapPlus_ext B sq _
    (fun N ↦ Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction B f)
      (upperStarLowerStarAdjunction B f')
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso B sq).hom)
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison B sq).hom)
      (pullbackSquareComparison_hom_app_factorsh B sq) N)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] freeRepresentableHomEquiv abelianHigherDirectImageClass

/-- The derived exchange mate acts on raw derived-Hom classes by inverse image.
This comparison involves no chart cohomology or inverse evaluation map.
Source: Stacks Project, Cohomology on Sites, Tags 0736 and 07A7; Tag 03Q8.
(blueprint: lem-kun-commutative-exchange-class-compatibility).

Proof: Put A = the free abelian sheaf represented by U and A' = the free
sheaf represented by its base change. The free-sheaf pullback isomorphism
identifies A' with g^* A. Apply the mate identity to the morphism
f^* A[0] -> F[0][q], inserting the exact inverse-image/single comparisons
at the source and target. The square comparison on singles is the single
of squareUpperStarIso, so its source is exactly commutativeExchangeRawSourceIso.
The mate is derivedBaseChangeMapPlus by their common derived-unit computation.
Commute the mate with the q-shift and apply zeroth homology. Naturality of
inverse-image/homology, its compatibility with the shift-to-q comparison,
and its single-complex identity give the displayed degree-q map. Evaluate
at the represented identity. The defining Hom equivalence for
abelianFreeRepresentablePullbackIso identifies this evaluation with the
unit for g on sections over U. All comparisons are natural isomorphisms;
the calculation also applies to q = 0, the zero sheaf and empty charts. -/
theorem commutativeExchangeClassCompatibility
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    let E :=
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).hom.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
            ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))
    E.hom.app (op (g.Etale.obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _).hom.app
        (op U) (abelianHigherDirectImageClass f q F U z)) =
      abelianHigherDirectImageClass f' q _ (g.Etale.obj U)
        (commutativeExchangeRawPullback sq F q U z) := by
  dsimp only
  let A := (abelianComparisonFree Y).obj U
  let A' := (abelianComparisonFree Y').obj (g.Etale.obj U)
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj
    (((g')^*[AddCommGrpCat.{u + 1}]).obj F)
  let P := ((g)^*[AddCommGrpCat.{u + 1}])
  let Q := ((g')^*[AddCommGrpCat.{u + 1}])
  let R := R+((f)_*[AddCommGrpCat.{u + 1}])
  let R' := R+((f')_*[AddCommGrpCat.{u + 1}])
  let adj := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
  let adj' := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').derivedPlus
  let θ := TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{u + 1} sq).hom
  have hβ : (mateEquiv adj adj' θ).natTrans =
      derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq :=
    derived_exchange_mate AddCommGrpCat.{u + 1} sq
  let e := abelianFreeRepresentablePullbackIso g U
  let δ := (DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
    (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app A
  let x := (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ z
  let b := commutativeExchangeRawPullback sq F q U z
  let c : Q.mapDerivedCategoryPlus.obj K ⟶ K' :=
    (Q.mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let T : P.mapDerivedCategoryPlus.obj (R.obj K) ⟶ R'.obj K' :=
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K ≫ R'.map c
  have hb : D+((f')^*[AddCommGrpCat.{u + 1}]).map δ ≫ θ.natTrans.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫ Q.mapDerivedCategoryPlus.map x ≫
      (Q.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app K ≫
        (shiftFunctor _ (q : ℤ)).map c =
    (((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A' ≫ b := by
    exact raw_pullback_source sq F q A A' e z
  let Hq' := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let v := higherClassMorphism f F q U z
  let v' := higherClassMorphism f' (Q.obj F) q (g.Etale.obj U) b
  let E : P.obj ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj (R.obj K)) ⟶
      Hq'.obj (R'.obj K') :=
    (P.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).hom.app (R.obj K) ≫ Hq'.map T
  have htrans := mate_homology_class
    ((f)^*[AddCommGrpCat.{u + 1}]) ((f')^*[AddCommGrpCat.{u + 1}]) P Q R R' adj adj' θ
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq) hβ A A' e.inv K K' q x
    ((((f')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A' ≫ b)
    c hb
  have hv : e.inv ≫ P.map v ≫ E = v' := by
    exact htrans
  exact class_sections_transport g U _ _ v v' E hv
    (abelianHigherDirectImageClass f q F U z)
    (abelianHigherDirectImageClass f' q (Q.obj F) (g.Etale.obj U) b)
    (higher_class_evaluation f F q U z)
    (higher_class_evaluation f' (Q.obj F) q (g.Etale.obj U) b)

end AlgebraicGeometry.Etale
