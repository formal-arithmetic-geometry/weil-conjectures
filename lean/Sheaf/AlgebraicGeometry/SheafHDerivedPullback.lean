/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation
public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import Mathlib.Util.TermReduce
import Sheaf.AlgebraicGeometry.SheafHDerivedNaturality
import all WeilConjectures.AlgebraicGeometry.DerivedSectionPullbackZero
import all WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport
import all WeilConjectures.AlgebraicGeometry.DerivedSectionSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero

/-! # Pullback compatibility of the fixed Ext evaluation -/

@[expose] public section
universe u v w t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
noncomputable section
set_option autoImplicit false

open CategoryTheory.Abelian RawRestrictedComparison
attribute [local instance 2200] CategoryTheory.Abelian.toPreadditive
attribute [local instance 2100] etaleComposition etaleIdentities etalePullbacks
  etaleBaseChange sheafifyInstance weakSheafifyInstance
attribute [local instance 2000] CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal
  HasSmallSiteSheafify.hasSheafify IsGrothendieckAbelian.hasExt
  HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat
  Scheme.enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat
attribute [local irreducible] derivedExtEvaluation sheafHToDerived rawAffineComplexPullback
  cohomologyMap upperStar Functor.rightDerivedFunctor Functor.mapDerivedCategory


private noncomputable def evalShift {C : Type*} [Category C] [HasShift C ℤ]
    (T : C ⥤ DerivedCategory AddCommGrpCat.{u + 1}) [T.CommShift ℤ]
    (q : ℕ) (B : C) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).obj
        (T.obj (B⟦(q : ℤ)⟧)) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj (T.obj B) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).mapIso
      ((T.commShiftIso (q : ℤ)).app B) ≪≫
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).app (T.obj B)

private noncomputable def evaluationAtSingle {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{u + 1} C]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (P : C ⥤ AddCommGrpCat.{u + 1}) [P.Additive] [PreservesFiniteLimits P]
    (A B : C) (q : ℕ) (g : P.obj A) (x : Ext A B q) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (P.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B)) :=
  (evalShift P.rightDerivedFunctor q ((DerivedCategory.singleFunctor C 0).obj B)).hom
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (P.rightDerivedFunctor.map (Ext.homEquiv x))
      ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
        P.rightDerivedZeroIsoSelf.app A).inv g))

private theorem derivedExtEvaluation_eq {C : Type v} [Category.{w} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{u + 1} C]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (P : C ⥤ AddCommGrpCat.{u + 1}) [P.Additive] [PreservesFiniteLimits P]
    (A B : C) (q : ℕ) (g : P.obj A) (x : Ext A B q) :
    derivedExtEvaluation P A B q g x =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (P.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app B))
        (evaluationAtSingle P A B q g x) := by
  simp only [derivedExtEvaluation, evaluationAtSingle, evalShift,
    Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rfl

private theorem evaluation_transport {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    (T : C ⥤ DerivedCategory AddCommGrpCat.{u + 1})
    (T' : D ⥤ DerivedCategory AddCommGrpCat.{u + 1}) (N : C ⥤ D)
    [T.CommShift ℤ] [T'.CommShift ℤ] [N.CommShift ℤ]
    (δ : T ⟶ N ⋙ T') [NatTrans.CommShift δ ℤ]
    (q : ℕ) (A B : C) (A' B' : D) (a : N.obj A ≅ A') (b : N.obj B ≅ B')
    (z : A ⟶ B⟦(q : ℤ)⟧) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map (T.map z) ≫
        (evalShift T q B).hom ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
          (δ.app B ≫ T'.map b.hom) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app A ≫ T'.map a.hom) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (T'.map (a.inv ≫ N.map z ≫ (N.commShiftIso (q : ℤ)).hom.app B ≫
            (shiftFunctor D (q : ℤ)).map b.hom)) ≫
        (evalShift T' q B').hom := by
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  have hs := transport_homology T T' N δ H₀ Hq (q : ℤ)
    (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).hom b.hom
    (Iso.refl (T.obj B)) (Iso.refl (T'.obj B'))
  simp only [Iso.refl_hom, Iso.refl_inv, Hq.map_id, Category.comp_id,
    Category.id_comp] at hs
  have hn := (Functor.whiskerRight δ H₀).naturality z
  dsimp only [Functor.comp_map, Functor.whiskerRight_app] at hn
  change H₀.map (T.map z) ≫ (evalShift T q B).hom ≫ Hq.map _ = _
  have hs' : H₀.map (δ.app (B⟦(q : ℤ)⟧)) ≫
      H₀.map (T'.map ((N.commShiftIso (q : ℤ)).hom.app B ≫
        (shiftFunctor D (q : ℤ)).map b.hom)) ≫ (evalShift T' q B').hom =
      (evalShift T q B).hom ≫ Hq.map (δ.app B ≫ T'.map b.hom) := by
    simpa only [evalShift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hs
  rw [← hs']
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  have ha : H₀.map (T'.map a.hom) ≫ H₀.map (T'.map a.inv) = 𝟙 _ := by
    rw [← H₀.map_comp, ← T'.map_comp, a.hom_inv_id, T'.map_id, H₀.map_id]
  rw [reassoc_of% ha]

private theorem evaluationAtSingle_pullback {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (P : C ⥤ AddCommGrpCat.{u + 1}) (R : D ⥤ AddCommGrpCat.{u + 1})
    [P.Additive] [R.Additive] [PreservesFiniteLimits P] [PreservesFiniteLimits R]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (δ : P.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    [NatTrans.CommShift δ ℤ] (A : C) (A' : D) (e : L.obj A ≅ A')
    (B : C) (q : ℕ) (g : P.obj A) (g' : R.obj A')
    (hg : (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (δ.app ((DerivedCategory.singleFunctor C 0).obj A) ≫
          R.rightDerivedFunctor.map
            ((L.mapDerivedCategorySingleFunctor 0).hom.app A ≫
              (DerivedCategory.singleFunctor D 0).map e.hom))
        ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
          P.rightDerivedZeroIsoSelf.app A).inv g) =
      (R.homologyRightDerivedFunctorObjSingleFunctorIso A' 0 ≪≫
        R.rightDerivedZeroIsoSelf.app A').inv g') (x : Ext A B q) :
    evaluationAtSingle R A' (L.obj B) q g'
        ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (zero_add q)) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (δ.app ((DerivedCategory.singleFunctor C 0).obj B) ≫
          R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app B))
        (evaluationAtSingle P A B q g x) := by
  let S := DerivedCategory.singleFunctor C 0
  let S' := DerivedCategory.singleFunctor D 0
  let a := (L.mapDerivedCategorySingleFunctor 0).app A ≪≫ S'.mapIso e
  let b := (L.mapDerivedCategorySingleFunctor 0).app B
  have hx : Ext.homEquiv ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (zero_add q)) =
      a.inv ≫ L.mapDerivedCategory.map (Ext.homEquiv x) ≫
        (L.mapDerivedCategory.commShiftIso (q : ℤ)).hom.app (S.obj B) ≫
        (shiftFunctor _ (q : ℤ)).map b.hom := by
    change ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (zero_add q)).hom = _
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, Ext.mapExactFunctor_hom]
    simp only [a, b, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
      ShiftedHom.map, Category.assoc]
    rfl
  have ht := evaluation_transport P.rightDerivedFunctor R.rightDerivedFunctor
    L.mapDerivedCategory δ q (S.obj A) (S.obj B) (S'.obj A') (S'.obj (L.obj B)) a b
    (Ext.homEquiv x)
  have hv := ConcreteCategory.congr_hom ht
    ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
      P.rightDerivedZeroIsoSelf.app A).inv g)
  simp only [AddCommGrpCat.comp_apply] at hv
  have hg' : (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
      (δ.app (S.obj A) ≫ R.rightDerivedFunctor.map a.hom)
      ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
        P.rightDerivedZeroIsoSelf.app A).inv g) =
    (R.homologyRightDerivedFunctorObjSingleFunctorIso A' 0 ≪≫
      R.rightDerivedZeroIsoSelf.app A').inv g' := by
    simpa only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using hg
  erw [hg'] at hv
  simp only [evaluationAtSingle, hx]
  exact hv.symm

private theorem single_pullback_formula {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (P : C ⥤ AddCommGrpCat.{u + 1}) (R : D ⥤ AddCommGrpCat.{u + 1})
    [P.Additive] [R.Additive] [PreservesFiniteLimits P] [PreservesFiniteLimits R]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (δ : P.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (B : C) (q : ℕ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (P.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app B)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (δ.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj B)) ≫
          R.rightDerivedFunctor.map
            (L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) ≫
              DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app B))) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (δ.app ((DerivedCategory.singleFunctor C 0).obj B) ≫
          R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app B)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (R.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ D 0).hom.app
          (L.obj B))) := by
  let j := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app B
  let j' := (DerivedCategory.singleFunctorIsoCompQ D 0).hom.app (L.obj B)
  have hf : L.mapDerivedCategory.map j ≫
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) ≫
        DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app B) =
      (L.mapDerivedCategorySingleFunctor 0).hom.app B ≫ j' := by
    simp only [j, j', DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app]
    erw [L.mapDerivedCategory.map_id, Category.id_comp, Category.comp_id]
    exact (single_factor L B).symm
  have hn := δ.naturality j
  dsimp only [Functor.comp_map] at hn
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [← Category.assoc, hn, Category.assoc, ← R.rightDerivedFunctor.map_comp, hf,
    R.rightDerivedFunctor.map_comp, Category.assoc]

private theorem derivedExtEvaluation_pullback {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (P : C ⥤ AddCommGrpCat.{u + 1}) (R : D ⥤ AddCommGrpCat.{u + 1})
    [P.Additive] [R.Additive] [PreservesFiniteLimits P] [PreservesFiniteLimits R]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (δ : P.rightDerivedFunctor ⟶ L.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    [NatTrans.CommShift δ ℤ] (A : C) (A' : D) (e : L.obj A ≅ A')
    (B : C) (q : ℕ) (g : P.obj A) (g' : R.obj A')
    (hg : (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        (δ.app ((DerivedCategory.singleFunctor C 0).obj A) ≫
          R.rightDerivedFunctor.map
            ((L.mapDerivedCategorySingleFunctor 0).hom.app A ≫
              (DerivedCategory.singleFunctor D 0).map e.hom))
        ((P.homologyRightDerivedFunctorObjSingleFunctorIso A 0 ≪≫
          P.rightDerivedZeroIsoSelf.app A).inv g) =
      (R.homologyRightDerivedFunctorObjSingleFunctorIso A' 0 ≪≫
        R.rightDerivedZeroIsoSelf.app A').inv g') (x : Ext A B q) :
    derivedExtEvaluation R A' (L.obj B) q g'
        ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (zero_add q)) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (δ.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj B)) ≫
          R.rightDerivedFunctor.map
            (L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) ≫
              DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app B)))
        (derivedExtEvaluation P A B q g x) := by
  let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  have he := evaluationAtSingle_pullback P R L δ A A' e B q g g' hg x
  have hc := ConcreteCategory.congr_hom (single_pullback_formula P R L δ B q)
    (evaluationAtSingle P A B q g x)
  simp only [AddCommGrpCat.comp_apply] at hc
  have hq := congrArg
    (fun y ↦ Hq.map (R.rightDerivedFunctor.map
      ((DerivedCategory.singleFunctorIsoCompQ D 0).hom.app (L.obj B))) y) he
  have ep := derivedExtEvaluation_eq P A B q g x
  have er := derivedExtEvaluation_eq R A' (L.obj B) q g'
    ((Ext.mk₀ e.inv).comp (x.mapExactFunctor L) (zero_add q))
  exact er.trans (hq.trans (hc.symm.trans (congrArg
    (fun y ↦ Hq.map
      (δ.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj B)) ≫
        R.rightDerivedFunctor.map
          (L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj B) ≫
            DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app B))) y)
    ep.symm)))

private theorem pullback_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let P := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    let R := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} f
    let e := P.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
      P.rightDerivedZeroIsoSelf.app M
    let e' := R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj M) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (L.obj M)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((derivedSectionPullback f).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
      e'.hom = e.hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f M := by
  dsimp only
  exact map_zero_comparison _ _
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0)
    _ _ _ _ _ _
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedSingleUnit_zero M)
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedSingleUnit_zero _)
    (derivedSectionPullback_single_unit f M)

private theorem pullback_generator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : AddCommGrpCat.{u + 1}) :
    (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app P ≫
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P) ≫
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app P) =
      (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app P := by
  let eX := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal
  let eY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal
  apply (cancel_mono (eX.hom.app _)).mp
  simp only [Category.assoc]
  rw [eX.hom.naturality]
  simp only [globalSectionsUpperStarMap, Category.assoc]
  simp only [eX, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  rw [show (constantSheafΓAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app P ≫
      eY.hom.app _ =
      (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).unit.app P from
      Adjunction.unit_rightAdjointUniq_hom_app _ _ P]
  rw [show (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app P ≫
      eX.hom.app _ =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).unit.app P from
      Adjunction.unit_rightAdjointUniq_hom_app _ _ P]
  exact Adjunction.unit_leftAdjointUniq_hom_app _ _ P

private theorem sheafHDerivedEquiv_apply {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H F q) :
    (sheafHDerivedEquiv F q).toEquiv.toFun x = sheafHToDerived F q x := rfl

private theorem evaluation_symm {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    sheafHToDerived F q ((sheafHDerivedEquiv F q).symm x) = x := by
  exact (sheafHDerivedEquiv_apply F q _).symm.trans
    ((sheafHDerivedEquiv F q).toEquiv.apply_symm_apply x)

private theorem inverse_evaluation {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : (cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)))
    (y : Sheaf.H F q) (h : sheafHToDerived F q y = x) :
    (sheafHDerivedEquiv F q).symm x = y := by
  exact ((sheafHDerivedEquiv F q).toEquiv.symm_apply_eq).2
    (h.symm.trans (sheafHDerivedEquiv_apply F q y).symm)

attribute [local irreducible] sheafHDerivedEquiv

private theorem natural_map_composite {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ D) (U : D ⥤ E) (H : E ⥤ F) (R : C ⥤ F)
    (z : J ⋙ U ⋙ H ⟶ R) {A : E} {B : D} {M N : C}
    (a : A ⟶ U.obj B) (b : B ⟶ J.obj M) (c : M ⟶ N)
    {K : F} (t : H.obj A ⟶ K) (s : K ⟶ R.obj M)
    (h : H.map (a ≫ U.map b) ≫ z.app M = t ≫ s) :
    H.map (a ≫ U.map (b ≫ J.map c)) ≫ z.app N = t ≫ s ≫ R.map c := by
  have hn := z.naturality c
  dsimp only [Functor.comp_map] at hn
  calc
    _ = H.map (a ≫ U.map b) ≫ H.map (U.map (J.map c)) ≫ z.app N := by
      simp only [Functor.map_comp, Category.assoc]
    _ = H.map (a ≫ U.map b) ≫ z.app M ≫ R.map c := by rw [hn]
    _ = _ := by rw [← Category.assoc, h, Category.assoc]

private theorem iso_square_generator {A B C D : AddCommGrpCat.{u + 1}}
    (z : A ≅ B) (z' : C ≅ D) (m : A ⟶ C) (s : B ⟶ D)
    (h : m ≫ z'.hom = z.hom ≫ s) (g : B) (g' : D) (hgen : s g = g') :
    m (z.inv g) = z'.inv g' := by
  apply (ConcreteCategory.bijective_of_isIso z'.hom).1
  have hh := ConcreteCategory.congr_hom h (z.inv g)
  simp only [AddCommGrpCat.comp_apply, Iso.inv_hom_id_apply] at hh ⊢
  exact hh.trans hgen

private theorem mapped_composite {C D E : Type*}
    [Category C] [Category D] [Category E] (R : C ⥤ D) (T : D ⥤ E)
    {A B : D} {X Y Z : C} (a : A ⟶ B) (b : B ⟶ R.obj X)
    (c : X ⟶ Y) (d : Y ⟶ Z) :
    T.map (a ≫ b ≫ R.map c) ≫ T.map (R.map d) =
      T.map ((a ≫ b) ≫ R.map (c ≫ d)) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem map_composite_apply {C D : Type*} [Category C] [Category D]
    (T : D ⥤ AddCommGrpCat.{u + 1}) (U : C ⥤ D) {A B C' : C}
    {G : AddCommGrpCat.{u + 1}} (p : G ⟶ T.obj (U.obj A)) (c : A ⟶ B)
    (k : B ⟶ C') (x : G) :
    (T.map (U.map k)).hom.toFun ((p ≫ T.map (U.map c)).hom.toFun x) =
      (p ≫ T.map (U.map (c ≫ k))).hom.toFun x := by
  rw [Functor.map_comp, Functor.map_comp]
  rfl

attribute [local irreducible] evaluationAtSingle evalShift
  upperStarComp Scheme.upperStarConstantSheafIso constantSheafΓAdj
  globalSectionsUpperStarMap

/-- Inverse fixed evaluation transports normalized chart restriction to Ext pullback.
This is the derived-presentation square for arbitrary abelian coefficients, before
coherent coefficient transport or evaluation of a raw higher-image class.
Source: Stacks Project, Tags 01FT and 03FD; derived adjunction is Tag 07A6.
Agent expansion of step 2 of lem-weil-pbc-affine-raw-evaluation-pullback.
(blueprint: lem-weil-pbc-sheaf-h-derived-pullback).

Proof: let b be the induced chart map and j,j' the two projections. Put
r = sheafHDerivedEquiv(j*F,q).symm(x). Represent r as a derived morphism from the
single constant integer sheaf to j*F[q]. Exact inverse image maps this morphism,
conjugated by its single and constant-sheaf comparisons. The constant comparison
sends the integer generator to the pulled-back generator by the adjunction-unit
formula. Apply derivedSectionPullback_single_unit to that constant sheaf.
Naturality of the derived unit and Leray comparison moves the represented
morphism through the comparison, and shift compatibility moves its shift through.
Apply zeroth homology and evaluate at the generator. The single-complex
factorization gives rawAffineComplexPullback followed by the exact inverse-image
single comparison. Coefficient naturality sheafHToDerived_map then inserts the
inverse upperStarComp(b,j,j') coefficient map. Functoriality identifies the resulting
map with normalizationCohomologyRestriction, by its definition. The forward fixed
evaluation of r is x, by inverse cancellation. Thus the forward evaluation of the
displayed right side is normalized restriction of x. Apply the inverse target
comparison and cancel its forward map. This proves the asserted equality, also
in degree zero, for identity maps, zero coefficients, and empty charts. -/
theorem sheafHDerivedEquiv_symm_restriction {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V V' : S.Etale) (h : V' ⟶ V) (x : rawAffineRestrictedCohomology f q F V) :
    (sheafHDerivedEquiv
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V'.hom f)).obj F) q).symm
        (normalizationCohomologyRestriction f q F h x) =
      Sheaf.H.map
        ((upperStarComp AddCommGrpCat.{u + 1} (normalizationChartMap f h)
          (pullback.snd V.hom f) (pullback.snd V'.hom f)
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).w.symm).inv.app
            F) q
        (cohomologyMap (normalizationChartMap f h)
          ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F) q
          ((sheafHDerivedEquiv
            ((upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F) q).symm x)) :=
  reduceProj% zeta% by
    let A := (upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F
    let B := (upperStar AddCommGrpCat.{u + 1} (pullback.snd V'.hom f)).obj F
    let b := normalizationChartMap f h
    let k : (upperStar AddCommGrpCat.{u + 1} b).obj A ⟶ B :=
      (upperStarComp AddCommGrpCat.{u + 1} b
        (pullback.snd V.hom f) (pullback.snd V'.hom f)
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).w.symm).inv.app F
    let r := (sheafHDerivedEquiv A q).symm x
    apply inverse_evaluation B q
    have hpull : sheafHToDerived ((upperStar AddCommGrpCat.{u + 1} b).obj A) q
          ((cohomologyMap b A q).toFun r) =
        (rawAffineComplexPullback (q : ℤ) b ((CochainComplex.singleFunctor _ 0).obj A) ≫
          (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
            (DerivedCategory.Q.map
              (((upperStar AddCommGrpCat.{u + 1} b).mapCochainComplexSingleFunctor 0).hom.app
                A))).hom.toFun (sheafHToDerived A q r) := by
      let P := Sheaf.Γ (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}
      let R := Sheaf.Γ (pullback V'.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}
      let L := upperStar AddCommGrpCat.{u + 1} b
      let Z := (constantSheaf (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))
      let Z' := (constantSheaf (pullback V'.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))
      let e : L.obj Z ≅ Z' := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} b).app _
      let S := DerivedCategory.singleFunctor
        (Sheaf (pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0
      let S' := DerivedCategory.singleFunctor
        (Sheaf (pullback V'.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0
      let a := (L.mapDerivedCategorySingleFunctor 0).app Z ≪≫ S'.mapIso e
      let δ := derivedSectionPullback b
      let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
      let Hq := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
      let zP := P.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
      let zR := R.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
      let g := (constantSheafΓAdj (pullback V.hom f).smallEtaleTopology
        AddCommGrpCat.{u + 1}).unit.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ULift.up 1)
      let g' := (constantSheafΓAdj (pullback V'.hom f).smallEtaleTopology
        AddCommGrpCat.{u + 1}).unit.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (ULift.up 1)
      have hz : H₀.map (δ.app (S.obj Z) ≫ R.rightDerivedFunctor.map a.hom) ≫
          zR.hom.app Z' = zP.hom.app Z ≫
            globalSectionsUpperStarMap AddCommGrpCat.{u + 1} b Z ≫ R.map e.hom := by
        simpa only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
          natural_map_composite S' R.rightDerivedFunctor H₀ R zR.hom
            (δ.app (S.obj Z)) ((L.mapDerivedCategorySingleFunctor 0).hom.app Z) e.hom
            (zP.hom.app Z) (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} b Z)
            (pullback_zero b Z)
      have hg : H₀.map (δ.app (S.obj Z) ≫ R.rightDerivedFunctor.map a.hom)
          (zP.inv.app Z g) = zR.inv.app Z' g' := by
        have hgen := ConcreteCategory.congr_hom
          (pullback_generator b (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (ULift.up 1)
        simp only [AddCommGrpCat.comp_apply] at hgen
        change R.map e.hom
          (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} b Z g) = g' at hgen
        exact iso_square_generator (zP.app Z) (zR.app Z')
          (H₀.map (δ.app (S.obj Z) ≫ R.rightDerivedFunctor.map a.hom))
          (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} b Z ≫ R.map e.hom)
          hz g g' hgen
      have : NatTrans.CommShift δ ℤ := pullback_commShift b
      have hraw : rawAffineComplexPullback (q : ℤ) b
            ((CochainComplex.singleFunctor _ 0).obj A) ≫
          (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
            (DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app A)) =
          Hq.map (δ.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj A)) ≫
            R.rightDerivedFunctor.map
              (L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor _ 0).obj A) ≫
                DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app A))) := by
        unfold rawAffineComplexPullback
        exact mapped_composite R.rightDerivedFunctor Hq _ _ _ _
      dsimp only [H₀, S, S', a, zP, zR] at hg
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso,
        NatIso.ofComponents_inv_app] at hg
      have hx : (cohomologyMap b A q).toFun r =
          (Ext.mk₀ e.inv).comp (r.mapExactFunctor L) (zero_add q) :=
        cohomologyMap_apply b A q r
      have heval := (congrArg (derivedExtEvaluation R Z' (L.obj A) q g') hx).trans
        (derivedExtEvaluation_pullback P R L δ Z Z' e A q g g' hg r)
      unfold sheafHToDerived
      change derivedExtEvaluation R Z' (L.obj A) q g' ((cohomologyMap b A q).toFun r) =
        (rawAffineComplexPullback (q : ℤ) b ((CochainComplex.singleFunctor _ 0).obj A) ≫
          (cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)).map
            (DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app A))).hom.toFun
          (derivedExtEvaluation P Z A q g r)
      exact heval.trans (ConcreteCategory.congr_hom hraw.symm (derivedExtEvaluation P Z A q g r))
    -- Insert coefficient transport and identify the prescribed restriction composite.
    have he : sheafHToDerived B q ((Sheaf.H.map k q).toFun ((cohomologyMap b A q).toFun r)) =
        normalizationCohomologyRestriction f q F h (sheafHToDerived A q r) := by
      let T := cohomology AddCommGrpCat.{u + 1} (pullback V'.hom f) (q : ℤ)
      let c := ((upperStar AddCommGrpCat.{u + 1} b).mapCochainComplexSingleFunctor 0).hom.app A
      let k' := (CochainComplex.singleFunctor _ 0).map k
      refine (sheafHToDerived_map k q ((cohomologyMap b A q).toFun r)).trans ?_
      refine (congrArg (fun y ↦ (T.map (DerivedCategory.Q.map k')).hom.toFun y) hpull).trans ?_
      unfold normalizationCohomologyRestriction
      exact map_composite_apply T DerivedCategory.Q _ c k' _
    have ha : sheafHToDerived A q r = x := evaluation_symm A q x
    exact he.trans (congrArg (normalizationCohomologyRestriction f q F h) ha)

end
end AlgebraicGeometry.Etale
