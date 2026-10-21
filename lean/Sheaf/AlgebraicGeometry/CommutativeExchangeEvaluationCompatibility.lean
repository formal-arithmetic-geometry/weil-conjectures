/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CommutativeExchangeRawPullback

import all Sheaf.AlgebraicGeometry.CommutativeExchangeClassCompatibility
import all WeilConjectures.AlgebraicGeometry.DerivedRestrictionZeroTransport
import all WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsSingle
import all WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport
import all WeilConjectures.AlgebraicGeometry.DerivedSectionPullbackZero
import WeilConjectures.AlgebraicGeometry.DerivedSectionSingleUnit
import all WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnit
import all WeilConjectures.AlgebraicGeometry.RestrictedComparisonGeneratorPullback
import WeilConjectures.SixFunctors.BaseChange.Sections

/-! # Compatibility of the chart pullback with raw evaluation

First prove derived evaluation naturality for an arbitrary square of exact
functors. For the geometric specialization, compute the ordinary section map
and its value on the represented identity generator.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

open RawRestrictedComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem zero_comparison_comp {C : Type*} [Category C]
    {A B B' C₀ D E E' F : C} (e : A ≅ D) (e' : C₀ ≅ F)
    (u : A ⟶ B) (v : B ⟶ B') (w : B' ⟶ C₀) (r : B ⟶ E) (r' : E ⟶ E')
    (s : E' ⟶ F) (p : D ⟶ E')
    (hv : v ≫ w ≫ e'.hom = r ≫ r' ≫ s) (hu : u ≫ r ≫ r' = e.hom ≫ p) :
    u ≫ v ≫ w = e.hom ≫ p ≫ s ≫ e'.inv := by
  apply (cancel_mono e'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hv]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ s) hu

section ExactSquare

variable {C D C' D' : Type*}
  [Category C] [Category D] [Category C'] [Category D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory D]
  [HasDerivedCategory.{u + 1} C'] [HasDerivedCategory D']
  (L : C ⥤ D) (M : D ⥤ D') (A : C ⥤ C') (L' : C' ⥤ D')
  [L.Additive] [M.Additive] [A.Additive] [L'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  (e : L ⋙ M ≅ A ⋙ L')

private noncomputable def exactSquareIso :
    L.mapDerivedCategory ⋙ M.mapDerivedCategory ≅
      A.mapDerivedCategory ⋙ L'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso L M).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso A L'

variable [EnoughInjectives D] [EnoughInjectives D']
  [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions D']
  (R : D ⥤ AddCommGrpCat.{u + 1}) [R.Additive] [PreservesFiniteLimits R]
  (R' : D' ⥤ AddCommGrpCat.{u + 1}) [R'.Additive] [PreservesFiniteLimits R']
  (δ : R.rightDerivedFunctor ⟶ M.mapDerivedCategory ⋙ R'.rightDerivedFunctor)

private noncomputable def exactSquareSectionMap :
    Evaluation.functor L R ⟶ A.mapDerivedCategoryPlus ⋙ Evaluation.functor L' R' :=
  Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ L.mapDerivedCategory) δ ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι (exactSquareIso L M A L' e).hom)
      R'.rightDerivedFunctor

private theorem exactSquareSectionMap_app (K : DerivedCategory.Plus C) :
    (exactSquareSectionMap L M A L' e R R' δ).app K =
      δ.app (L.mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj K)) ≫
        R'.rightDerivedFunctor.map
          ((exactSquareIso L M A L' e).hom.app (DerivedCategory.Plus.ι.obj K)) := by
  rfl

private theorem exactSquare_zero_of_single_unit (G : C)
    (s : R.obj (L.obj G) ⟶ R'.obj (M.obj (L.obj G)))
    (hs : R.rightDerivedSingleUnit (L.obj G) ≫
      δ.app ((DerivedCategory.singleFunctor _ 0).obj (L.obj G)) ≫
      R'.rightDerivedFunctor.map
        ((M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)) =
      (DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} 0).map s ≫
        R'.rightDerivedSingleUnit (M.obj (L.obj G))) :
      let b := L.mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app G
      let c := M.mapDerivedCategory.map b.hom ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
      let z := R'.homologyRightDerivedFunctorObjSingleFunctorIso (M.obj (L.obj G)) 0 ≪≫
        R'.rightDerivedZeroIsoSelf.app (M.obj (L.obj G))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R'.rightDerivedFunctor.map c) ≫ z.hom =
        (Evaluation.zeroIso L R G).hom ≫ s := by
  extract_lets b c z
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
  let N := L.obj G
  let zF := R.homologyRightDerivedFunctorObjSingleFunctorIso N 0 ≪≫
    R.rightDerivedZeroIsoSelf.app N
  have hF := R.rightDerivedSingleUnit_zero N
  have hR := R'.rightDerivedSingleUnit_zero (M.obj N)
  change H.map (R.rightDerivedSingleUnit N) ≫ zF.hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0).hom.app
      (R.obj N) at hF
  change H.map (R'.rightDerivedSingleUnit (M.obj N)) ≫ z.hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0).hom.app
      (R'.obj (M.obj N)) at hR
  have hs0 := map_zero_comparison H
    (DerivedCategory.singleFunctor AddCommGrpCat.{u + 1} 0)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u + 1} 0)
    zF z (R.rightDerivedSingleUnit N) (R'.rightDerivedSingleUnit (M.obj N))
    (δ.app ((DerivedCategory.singleFunctor _ 0).obj N) ≫
      R'.rightDerivedFunctor.map ((M.mapDerivedCategorySingleFunctor 0).hom.app N))
    s hF hR hs
  simp only [Functor.map_comp, Category.assoc] at hs0
  change H.map (δ.app _) ≫ H.map (R'.rightDerivedFunctor.map c) ≫ z.hom =
    (Evaluation.zeroIso L R G).hom ≫ s
  dsimp only [c]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := (Functor.whiskerRight δ H).naturality b.hom
  dsimp only [Functor.comp_map, Functor.whiskerRight_app] at hnH
  erw [← reassoc_of% hnH]
  exact (congrArg (fun t ↦ H.map (R.rightDerivedFunctor.map b.hom) ≫ t) hs0).trans
    (Category.assoc (H.map (R.rightDerivedFunctor.map b.hom)) zF.hom s).symm

private theorem exactSquareSectionMap_zero (G : C) (G' : C') (ψ : A.obj G ⟶ G')
    (s : R.obj (L.obj G) ⟶ R'.obj (M.obj (L.obj G)))
    (hδ :
      let b := L.mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app G
      let c := M.mapDerivedCategory.map b.hom ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
      let z := R'.homologyRightDerivedFunctorObjSingleFunctorIso (M.obj (L.obj G)) 0 ≪≫
        R'.rightDerivedZeroIsoSelf.app (M.obj (L.obj G))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R'.rightDerivedFunctor.map c) ≫ z.hom =
        (Evaluation.zeroIso L R G).hom ≫ s) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((exactSquareSectionMap L M A L' e R R' δ).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      (Evaluation.functor L' R' ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map ψ) =
    (Evaluation.zeroIso L R G).hom ≫ s ≫
      R'.map (e.hom.app G ≫ L'.map ψ) ≫ (Evaluation.zeroIso L' R' G').inv := by
  have ht := square_zero_transport L M A L' R' e G G' ψ
  dsimp only at ht hδ
  rw [exactSquareSectionMap_app,
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map_comp]
  exact zero_comparison_comp (Evaluation.zeroIso L R G) (Evaluation.zeroIso L' R' G')
    _ _ _ _ _ _ _ ht hδ

private theorem exactSquareSectionMap_single (F : C) (F' : C') (φ : A.obj F ⟶ F') :
    (exactSquareSectionMap L M A L' e R R' δ).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (Evaluation.functor L' R').map
        ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map φ) ≫
      (Evaluation.singleIso L' R' F').hom =
    (Evaluation.singleIso L R F).hom ≫
      δ.app (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (L.obj F))) ≫
      R'.rightDerivedFunctor.map
        (M.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor _ 0).obj (L.obj F)) ≫
          DerivedCategory.Q.map
            ((M.mapCochainComplexSingleFunctor 0).hom.app _ ≫
              (CochainComplex.singleFunctor _ 0).map (e.hom.app F ≫ L'.map φ))) := by
  rw [evaluation_single L R F, evaluation_single L' R' F']
  rw [exactSquareSectionMap_app]
  change (δ.app (L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
      R'.rightDerivedFunctor.map ((exactSquareIso L M A L' e).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj F))) ≫
    R'.rightDerivedFunctor.map (L'.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
      ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ))) ≫
    R'.rightDerivedFunctor.map ((L'.mapDerivedCategorySingleFunctor 0).hom.app F') = _
  rw [plus_single_map A F F' φ]
  exact single_sections_expanded L M A L' e
    R.rightDerivedFunctor R'.rightDerivedFunctor δ F F' φ

private theorem exactSquareSectionMap_commShift [NatTrans.CommShift δ ℤ] :
    NatTrans.CommShift (exactSquareSectionMap L M A L' e R R' δ) ℤ := by
  let I := (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C)
  let I' := (DerivedCategory.Plus.ι : DerivedCategory.Plus C' ⥤ DerivedCategory C')
  let N := A.mapDerivedCategory
  let P := L.mapDerivedCategory ⋙ R.rightDerivedFunctor
  let Q := L'.mapDerivedCategory ⋙ R'.rightDerivedFunctor
  let N' := A.mapDerivedCategoryPlus
  have hcomp : NatTrans.CommShift A.mapDerivedCategoryPlusCompatibility.inv ℤ := by
    change NatTrans.CommShift
      (DerivedCategory.TStructure.t.plus.liftCompιIso
        (I ⋙ N) (fun X ↦ (N'.obj X).2)).inv ℤ
    infer_instance
  have hs : NatTrans.CommShift (exactSquareIso L M A L' e).hom ℤ := by
    dsimp only [exactSquareIso, Iso.trans_hom, Iso.symm_hom]
    have : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso L M).inv ℤ :=
      NatTrans.CommShift.of_iso_inv _ ℤ
    infer_instance
  let β : P ⟶ N ⋙ Q :=
    Functor.whiskerLeft L.mapDerivedCategory δ ≫
      (Functor.associator L.mapDerivedCategory M.mapDerivedCategory R'.rightDerivedFunctor).inv ≫
      Functor.whiskerRight (exactSquareIso L M A L' e).hom R'.rightDerivedFunctor ≫
      (Functor.associator N L'.mapDerivedCategory R'.rightDerivedFunctor).hom
  have : NatTrans.CommShift β ℤ := by
    dsimp only [β]
    infer_instance
  have heq : exactSquareSectionMap L M A L' e R R' δ =
      Functor.whiskerLeft I β ≫ (Functor.associator I N Q).inv ≫
        Functor.whiskerRight A.mapDerivedCategoryPlusCompatibility.inv Q ≫
        (Functor.associator N' I' Q).hom := by
    ext K
    dsimp only [exactSquareSectionMap, β, I, I', P, Q, N, N',
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
      Functor.mapDerivedCategoryPlusCompatibility, Functor.mapDerivedCategoryPlus]
    erw [L'.mapDerivedCategory.map_id, R'.rightDerivedFunctor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm
  exact lift_composite_commShift I I' N N' P Q β A.mapDerivedCategoryPlusCompatibility
    (exactSquareSectionMap L M A L' e R R' δ) heq

private theorem exactSquareSectionMap_shift [NatTrans.CommShift δ ℤ]
    (q : ℕ) (F : C) (F' : C') (φ : A.obj F ⟶ F') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((exactSquareSectionMap L M A L' e R R' δ).app
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)) ≫
      (Evaluation.functor L' R' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
        ((A.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ (q : ℤ)).map
            ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
              (DerivedCategory.Plus.singleFunctor _ 0).map φ)) ≫
      (Evaluation.shiftIso L' R' q F').hom =
    (Evaluation.shiftIso L R q F).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (δ.app (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (R'.rightDerivedFunctor.map
          (M.mapDerivedCategoryFactors.hom.app
            ((CochainComplex.singleFunctor _ 0).obj (L.obj F)) ≫
          DerivedCategory.Q.map
            ((M.mapCochainComplexSingleFunctor 0).hom.app _ ≫
              (CochainComplex.singleFunctor _ 0).map (e.hom.app F ≫ L'.map φ)))) := by
  let N := A.mapDerivedCategoryPlus
  let T' := Evaluation.functor L' R'
  let τ := exactSquareSectionMap L M A L' e R R' δ
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let f := (A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let j := Evaluation.singleIso L R F
  let j' := Evaluation.singleIso L' R' F'
  have hs := exactSquareSectionMap_single L M A L' e R R' δ F F' φ
  have : NatTrans.CommShift τ ℤ := exactSquareSectionMap_commShift L M A L' e R R' δ
  rw [evaluation_shift_transport L L' R R' N τ q F F' f]
  change (Evaluation.shiftIso L R q F).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (j.inv ≫ τ.app K ≫ T'.map f ≫ j'.hom) = _
  change τ.app K ≫ T'.map f ≫ j'.hom = _ at hs
  rw [hs]
  dsimp only [j]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp, Category.assoc]


private noncomputable def exactSquareCohomologyMap
    (q : ℕ) (F : C) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (R.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) ⟶
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (R'.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (L'.obj (A.obj F))))) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
      (δ.app (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor _ 0).obj (L.obj F))) ≫
        R'.rightDerivedFunctor.map (M.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) ≫
    (R'.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
        (DerivedCategory.Q.map
          ((M.mapCochainComplexSingleFunctor 0).hom.app _ ≫
            (CochainComplex.singleFunctor _ 0).map (e.hom.app F)))

private theorem exactSquareCohomologyMap_expand (q : ℕ) (F : C) :
    exactSquareCohomologyMap L M A L' e R R' δ q F =
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
            (δ.app (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).map
            (R'.rightDerivedFunctor.map
              (M.mapDerivedCategoryFactors.hom.app
                ((CochainComplex.singleFunctor _ 0).obj (L.obj F)) ≫
              DerivedCategory.Q.map
                ((M.mapCochainComplexSingleFunctor 0).hom.app _ ≫
                  (CochainComplex.singleFunctor _ 0).map (e.hom.app F))))
    := by
  simp only [exactSquareCohomologyMap, Functor.comp_map, Functor.map_comp, Category.assoc]

private theorem exactSquareEvaluation_pullback [NatTrans.CommShift δ ℤ]
    (q : ℕ) (G : C) (G' : C') (ε : A.obj G ≅ G')
    (F : C)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    (s : R.obj (L.obj G) ⟶ R'.obj (M.obj (L.obj G)))
    (hδ :
      let b := L.mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app G
      let c := M.mapDerivedCategory.map b.hom ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
      let z := R'.homologyRightDerivedFunctorObjSingleFunctorIso (M.obj (L.obj G)) 0 ≪≫
        R'.rightDerivedZeroIsoSelf.app (M.obj (L.obj G))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R'.rightDerivedFunctor.map c) ≫ z.hom =
        (Evaluation.zeroIso L R G).hom ≫ s) :
    let H := Evaluation.functor L R ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
    let H' := Evaluation.functor L' R' ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0
    H.map z ≫ (Evaluation.shiftIso L R q F).hom ≫
        exactSquareCohomologyMap L M A L' e R R' δ q F =
      (Evaluation.zeroIso L R G).hom ≫ s ≫
        R'.map (e.hom.app G ≫ L'.map ε.hom) ≫
        (Evaluation.zeroIso L' R' G').inv ≫
        H'.map ((DerivedCategory.Plus.singleFunctor _ 0).map ε.inv ≫
          (A.mapDerivedCategoryPlusSingleFunctor 0).inv.app G ≫
          A.mapDerivedCategoryPlus.map z ≫
          (A.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ (q : ℤ)).map
            ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
        (Evaluation.shiftIso L' R' q (A.obj F)).hom := by
  intro H H'
  let K₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let K₁ := ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧
  let α := (A.mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map ε.hom
  let αinv := (DerivedCategory.Plus.singleFunctor _ 0).map ε.inv ≫
    (A.mapDerivedCategoryPlusSingleFunctor 0).inv.app G
  let β := (A.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  let τ := Functor.whiskerRight (exactSquareSectionMap L M A L' e R R' δ)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
  have hα : α ≫ αinv = 𝟙 _ := by
    dsimp only [α, αinv]
    simp only [Category.assoc]
    rw [← (DerivedCategory.Plus.singleFunctor C' 0).map_comp_assoc, Iso.hom_inv_id]
    rw [(DerivedCategory.Plus.singleFunctor C' 0).map_id, Category.id_comp]
    exact (A.mapDerivedCategoryPlusSingleFunctor 0).hom_inv_id_app G
  have hz := exactSquareSectionMap_zero L M A L' e R R' δ G G' ε.hom s hδ
  have hs := exactSquareSectionMap_shift L M A L' e R R' δ q F (A.obj F) (𝟙 _)
  simp only [L'.map_id, (DerivedCategory.Plus.singleFunctor C' 0).map_id,
    Category.comp_id] at hs
  erw [Category.comp_id, Category.comp_id] at hs
  change τ.app K₀ ≫ H'.map α = _ at hz
  change τ.app K₁ ≫ H'.map β ≫ _ = _ at hs
  have hn : H.map z ≫ τ.app K₁ = τ.app K₀ ≫
      H'.map (A.mapDerivedCategoryPlus.map z) := τ.naturality z
  have hc : H'.map α ≫ H'.map αinv = 𝟙 _ := by
    rw [← Functor.map_comp, hα]
    exact H'.map_id _
  calc
    _ = H.map z ≫ τ.app K₁ ≫ H'.map β ≫
        (Evaluation.shiftIso L' R' q (A.obj F)).hom := by
      rw [exactSquareCohomologyMap_expand, hs]
    _ = τ.app K₀ ≫ H'.map (A.mapDerivedCategoryPlus.map z) ≫ H'.map β ≫
        (Evaluation.shiftIso L' R' q (A.obj F)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ H'.map β ≫ (Evaluation.shiftIso L' R' q (A.obj F)).hom) hn
    _ = _ := by
      simp only [← Category.assoc] at hz ⊢
      rw [← hz]
      simp only [Category.assoc]
      have h : τ.app K₀ ≫ H'.map (A.mapDerivedCategoryPlus.map z) ≫ H'.map β ≫
          (Evaluation.shiftIso L' R' q (A.obj F)).hom =
          (τ.app K₀ ≫ H'.map α) ≫
            H'.map (αinv ≫ A.mapDerivedCategoryPlus.map z ≫ β) ≫
            (Evaluation.shiftIso L' R' q (A.obj F)).hom := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← Category.assoc (H'.map α), hc]
        simp only [Category.id_comp]
      simpa only [αinv, β, Category.assoc] using h


private theorem exactSquareEvaluation_value [NatTrans.CommShift δ ℤ]
    (q : ℕ) (G : C) (G' : C') (ε : A.obj G ≅ G')
    (F : C)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    (s : R.obj (L.obj G) ⟶ R'.obj (M.obj (L.obj G)))
    (hδ :
      let b := L.mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app G
      let c := M.mapDerivedCategory.map b.hom ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
      let z := R'.homologyRightDerivedFunctorObjSingleFunctorIso (M.obj (L.obj G)) 0 ≪≫
        R'.rightDerivedZeroIsoSelf.app (M.obj (L.obj G))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R'.rightDerivedFunctor.map c) ≫ z.hom =
        (Evaluation.zeroIso L R G).hom ≫ s)
    (γ : R.obj (L.obj G)) (γ' : R'.obj (L'.obj G'))
    (hγ : R'.map (e.hom.app G ≫ L'.map ε.hom) (s γ) = γ') :
    exactSquareCohomologyMap L M A L' e R R' δ q F
      (commutativeExchangeEvaluation L R q G F z γ) =
      commutativeExchangeEvaluation L' R' q G' (A.obj F)
        (commutativeExchangeTransport A q ε z) γ' := by
  simp only [commutativeExchangeEvaluation_def]
  rw [commutativeExchangeTransport_def]
  have h := exactSquareEvaluation_pullback L M A L' e R R' δ q G G' ε F z s hδ
  dsimp only at h
  have hp := congrArg (fun m ↦ m ((Evaluation.zeroIso L R G).inv γ)) h
  simp only [ConcreteCategory.comp_apply] at hp
  erw [Iso.inv_hom_id_apply, hγ] at hp
  exact hp

private theorem exactSquareEvaluation_hom [NatTrans.CommShift δ ℤ]
    (q : ℕ) (G : C) (G' : C') (ε : A.obj G ≅ G')
    (F : C)
    (s : R.obj (L.obj G) ⟶ R'.obj (M.obj (L.obj G)))
    (hδ :
      let b := L.mapDerivedCategory.mapIso
          ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app G
      let c := M.mapDerivedCategory.map b.hom ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
      let z := R'.homologyRightDerivedFunctorObjSingleFunctorIso (M.obj (L.obj G)) 0 ≪≫
        R'.rightDerivedZeroIsoSelf.app (M.obj (L.obj G))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (δ.app (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (R'.rightDerivedFunctor.map c) ≫ z.hom =
        (Evaluation.zeroIso L R G).hom ≫ s)
    (γ : R.obj (L.obj G)) (γ' : R'.obj (L'.obj G'))
    (hγ : R'.map (e.hom.app G ≫ L'.map ε.hom) (s γ) = γ') :
    commutativeExchangeEvaluationHom L R q G F γ ≫
        exactSquareCohomologyMap L M A L' e R R' δ q F =
      commutativeExchangeTransportHom A q ε ≫
        commutativeExchangeEvaluationHom L' R' q G' (A.obj F) γ' := by
  apply ConcreteCategory.hom_ext
  intro z
  simp only [ConcreteCategory.comp_apply]
  erw [commutativeExchangeEvaluationHom_apply, commutativeExchangeTransportHom_apply,
    commutativeExchangeEvaluationHom_apply]
  exact exactSquareEvaluation_value L M A L' e R R' δ q G G' ε F z s hδ γ γ' hγ

end ExactSquare

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.rightDerivedFunctorPlus
  exactSquareCohomologyMap derivedSectionPullback

private noncomputable def chartRestrictionSquare {X X' : Scheme.{u}} (a : X' ⟶ X)
    (W : X.Etale) (W' : X'.Etale) (t : W'.left ⟶ W.left)
    (hw : t ≫ W.hom = W'.hom ≫ a) :
    upperStar AddCommGrpCat.{u + 1} (Z := W.left) (Y := X) W.hom ⋙
        upperStar AddCommGrpCat.{u + 1} (Z := W'.left) (Y := W.left) t ≅
      upperStar AddCommGrpCat.{u + 1} a ⋙
        upperStar AddCommGrpCat.{u + 1} (Z := W'.left) (Y := X') W'.hom :=
  (upperStarComp AddCommGrpCat.{u + 1} (T := W'.left) (S := W.left) (R := X) t W.hom).symm ≪≫
    upperStarComp AddCommGrpCat.{u + 1} (T := W'.left) (S := X') (R := X) W'.hom a (t ≫ W.hom) hw

private theorem rawAffineComplexPullback_eq (q : ℤ) {X Y : Scheme.{u}} (t : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    rawAffineComplexPullback q t K =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map
        ((derivedSectionPullback (X := X) (Y := Y) t).app (DerivedCategory.Q.obj K) ≫
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
            ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategoryFactors.hom.app K)) := by
  simp only [rawAffineComplexPullback, derivedSectionPullback, rightDerivedGlobalSections,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Category.assoc]

private theorem chartCohomologyMap_eq
    {X X' V V' : Scheme.{u}} (a : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X')
    (t : V' ⟶ V) (hw : t ≫ p = p' ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let L := upperStar AddCommGrpCat.{u + 1} p
    let M := upperStar AddCommGrpCat.{u + 1} t
    let P := upperStar AddCommGrpCat.{u + 1} a
    let L' := upperStar AddCommGrpCat.{u + 1} p'
    let e := (upperStarComp AddCommGrpCat.{u + 1} t p).symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} p' a (t ≫ p) hw
    let R := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
    let R' := Sheaf.Γ V'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let c : M.obj (L.obj F) ⟶ L'.obj (P.obj F) := e.hom.app F
    exactSquareCohomologyMap L M P L' e R R' (derivedSectionPullback t) q F =
      rawAffineComplexPullback (q : ℤ) t ((CochainComplex.singleFunctor _ 0).obj (L.obj F)) ≫
        (cohomology AddCommGrpCat.{u + 1} V' (q : ℤ)).map
          (DerivedCategory.Q.map
            ((M.mapCochainComplexSingleFunctor 0).hom.app _ ≫
              (CochainComplex.singleFunctor _ 0).map c)) := by
  dsimp only
  simp only [exactSquareCohomologyMap, rawAffineComplexPullback_eq,
    cohomology, rightDerivedGlobalSections, Functor.comp_map]

private theorem chartEvaluation_hom
    {X X' V V' : Scheme.{u}} (a : X' ⟶ X) (p : V ⟶ X) (p' : V' ⟶ X')
    (t : V' ⟶ V) (hw : t ≫ p = p' ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ε : ((a)^*[AddCommGrpCat.{u + 1}]).obj G ≅ G')
    (γ : (Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (((p)^*[AddCommGrpCat.{u + 1}]).obj G))
    (γ' : (Sheaf.Γ V'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (((p')^*[AddCommGrpCat.{u + 1}]).obj G'))
    (hγ : (Sheaf.Γ V'.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((((upperStarComp AddCommGrpCat.{u + 1} t p).symm ≪≫
          upperStarComp AddCommGrpCat.{u + 1} p' a (t ≫ p) hw).hom.app G) ≫
        ((p')^*[AddCommGrpCat.{u + 1}]).map ε.hom)
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t
        (((p)^*[AddCommGrpCat.{u + 1}]).obj G) γ) = γ') :
    let L := upperStar AddCommGrpCat.{u + 1} p
    let M := upperStar AddCommGrpCat.{u + 1} t
    let P := upperStar AddCommGrpCat.{u + 1} a
    let L' := upperStar AddCommGrpCat.{u + 1} p'
    let e := (upperStarComp AddCommGrpCat.{u + 1} t p).symm ≪≫
      upperStarComp AddCommGrpCat.{u + 1} p' a (t ≫ p) hw
    let R := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
    let R' := Sheaf.Γ V'.smallEtaleTopology AddCommGrpCat.{u + 1}
    commutativeExchangeEvaluationHom L R q G F γ ≫
        exactSquareCohomologyMap L M P L' e R R' (derivedSectionPullback t) q F =
      commutativeExchangeTransportHom P q ε ≫
        commutativeExchangeEvaluationHom L' R' q G' (P.obj F) γ'  := by
  intro L M P L' e R R'
  let δ : R.rightDerivedFunctor ⟶ M.mapDerivedCategory ⋙ R'.rightDerivedFunctor := by
    have d := derivedSectionPullback (X := V') (Y := V) t
    dsimp only [rightDerivedGlobalSections] at d
    exact d
  have : NatTrans.CommShift δ ℤ := by
    have hs := pullback_commShift (X := V') (Y := V) t
    dsimp only [rightDerivedGlobalSections, commShiftRightDerivedGlobalSections] at hs
    exact hs
  exact exactSquareEvaluation_hom L M P L' e R R' δ q G G' ε F
    (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t (L.obj G))
    (exactSquare_zero_of_single_unit L M R R' δ G
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t (L.obj G))
      (by
        simpa only [δ, derivedSectionPullback, rightDerivedGlobalSections] using
          derivedSectionPullback_single_unit t (L.obj G))) γ γ' hγ

private theorem globalSections_identity {X Y : Scheme.{u}} (m : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let A := AddCommGrpCat.{u + 1}
    let wF : Y.Etale := Scheme.Etale.mk (𝟙 Y)
    let wG : X.Etale := Scheme.Etale.mk (𝟙 X)
    let tF := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) Y)
    let tG := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) X)
    let K := (upperStar A m).obj F
    let theta : wG ⟶ (MorphismProperty.Over.pullback @Etale ⊤ m).obj wF :=
      MorphismProperty.Over.homMk (pullback.lift m (𝟙 X)
        ((Category.comp_id m).trans (Category.id_comp m).symm)) (by simp [wG])
    globalSectionsUpperStarMap A m F ≫ tG.hom.app K =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op := by
  intro A wF wG tF tG K theta
  let a : wF ⟶ ⊤_ Y.Etale := terminal.from _
  let c : wG ⟶ ⊤_ X.Etale := terminal.from _
  have hG : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op wG) = K.obj.map c.op := by
    erw [← Sheaf.ΓRes_map K c.op, ← terminalEvaluation_eq_res _ _ terminalIsTerminal K]
    simp only [Iso.inv_hom_id_app_assoc]
  have hterm : c ≫ (PreservesTerminal.iso m.Etale).inv =
      theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ m).map a := by
    exact (terminalIsTerminal.isTerminalObj m.Etale).hom_ext _ _
  simp only [globalSectionsUpperStarMap, tF, tG, terminalEvaluation_eq_res,
    Category.assoc]
  change F.ΓRes (op (⊤_ Y.Etale)) ≫
    ((upperStarLowerStarAdjunction A m).unit.app F).hom.app _ ≫
    K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
    K.ΓRes (op wG) = _
  erw [hG]
  have hmaps : K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ K.obj.map c.op =
      K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op ≫
        K.obj.map theta.op := by
    rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
  erw [hmaps]
  have hn := ((upperStarLowerStarAdjunction A m).unit.app F).hom.naturality a.op
  change F.obj.map a.op ≫ _ = _ ≫
    K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op at hn
  erw [← reassoc_of% hn]
  erw [← Sheaf.ΓRes_map F a.op]
  rfl

private theorem etaleObjectSections_pullback {X X' : Scheme.{u}} (h : X' ⟶ X)
    (Vf : X.Etale) (Vg : X'.Etale) (m : Vg.left ⟶ Vf.left)
    (hm' : m ≫ Vf.hom = Vg.hom ≫ h) (i : Vg.left ⟶ pullback Vf.hom h)
    (hi₁ : i ≫ pullback.fst _ _ = m) (hi₂ : i ≫ pullback.snd _ _ = Vg.hom)
    [IsIso i] (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let b : Vg ⟶ h.Etale.obj Vf := MorphismProperty.Over.homMk i hi₂
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app H).hom.app
        (op Vf) ≫ ((upperStar AddCommGrpCat.{u + 1} h).obj H).obj.map b.op) ≫
      (etaleObjectSectionsIso Vg).hom.app ((upperStar AddCommGrpCat.{u + 1} h).obj H) =
    (etaleObjectSectionsIso Vf).hom.app H ≫
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} m
        ((upperStar AddCommGrpCat.{u + 1} (Z := Vf.left) (Y := X) Vf.hom).obj H) ≫
      (Sheaf.Γ Vg.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((chartRestrictionSquare h Vf Vg m hm').hom.app H) := by
  intro b₀
  let A := AddCommGrpCat.{u + 1}
  obtain ⟨hp', hu⟩ := etale_restriction_pullback_unit h Vf.hom m Vg.hom hm' i hi₁ hi₂
  have huH := hu H
  dsimp only at huH
  let F := (upperStar A (Z := Vf.left) (Y := X) Vf.hom).obj H
  let G := (upperStar A h).obj H
  let K := (upperStar A (Z := Vg.left) (Y := Vf.left) m).obj F
  let k := (upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
    (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H
  let wF : Vf.left.Etale := Scheme.Etale.mk (𝟙 Vf.left)
  let wG : Vg.left.Etale := Scheme.Etale.mk (𝟙 Vg.left)
  let eF : (MorphismProperty.Over.map ⊤ (inferInstance : Etale Vf.hom)).obj wF ≅ Vf :=
    MorphismProperty.Over.isoMk (Iso.refl Vf.left) (by simp [wF])
  let eG : (MorphismProperty.Over.map ⊤ hp').obj wG ≅ Vg :=
    MorphismProperty.Over.isoMk (Iso.refl Vg.left) (by simp [wG])
  let rF := (upperStarIsoLocalizationRestriction A Vf.hom inferInstance).app H
  let rG := (upperStarIsoLocalizationRestriction A Vg.hom hp').app G
  let tF := Sheaf.ΓNatIsoSheafSections Vf.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vf.left)
  let tG := Sheaf.ΓNatIsoSheafSections Vg.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vg.left)
  let theta : wG ⟶ (MorphismProperty.Over.pullback @Etale ⊤ m).obj wF :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 Vg.left)
      ((Category.comp_id m).trans (Category.id_comp m).symm)) (by simp [wG])
  let b : Vg ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Vf :=
    MorphismProperty.Over.homMk i hi₂
  have ht : globalSectionsUpperStarMap A m F ≫ tG.hom.app K =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op := by
    exact globalSections_identity m F
  have hEF : (etaleObjectSectionsIso Vf).hom.app H =
      H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ tF.inv.app F := by rfl
  have hEG : (etaleObjectSectionsIso Vg).hom.app G =
      G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
        tG.inv.app ((upperStar A (Z := Vg.left) (Y := X') Vg.hom).obj G) := by rfl
  change ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
      K.obj.map theta.op ≫ k.hom.app (op wG) ≫ rG.hom.hom.app (op wG) ≫
        G.obj.map eG.inv.op =
    rF.hom.hom.app (op wF) ≫ H.obj.map eF.inv.op ≫
      ((upperStarLowerStarAdjunction A h).unit.app H).hom.app (op Vf) ≫
        G.obj.map b.op at huH
  have hz := congrArg (fun a ↦ H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ a ≫
    G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
      tG.inv.app ((upperStar A (Z := Vg.left) (Y := X') Vg.hom).obj G)) huH
  have hrG : rG.hom.hom.app (op wG) ≫ rG.inv.hom.app (op wG) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have hrF : rF.inv.hom.app (op wF) ≫ rF.hom.hom.app (op wF) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have heG : G.obj.map eG.inv.op ≫ G.obj.map eG.hom.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id]
    exact G.obj.map_id _
  have heF : H.obj.map eF.hom.op ≫ H.obj.map eF.inv.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id]
    exact H.obj.map_id _
  simp only [Category.assoc] at hz
  rw [reassoc_of% heG, reassoc_of% hrG, reassoc_of% hrF, reassoc_of% heF] at hz
  change (((upperStarLowerStarAdjunction A h).unit.app H).hom.app (op Vf) ≫
    G.obj.map b.op) ≫ (etaleObjectSectionsIso Vg).hom.app G =
    (etaleObjectSectionsIso Vf).hom.app H ≫ globalSectionsUpperStarMap A m F ≫
      (Sheaf.Γ Vg.left.smallEtaleTopology A).map k
  rw [hEF, hEG]
  have hn := tG.inv.naturality k
  change k.hom.app (op wG) ≫ tG.inv.app _ = tG.inv.app K ≫
    (Sheaf.Γ Vg.left.smallEtaleTopology A).map k at hn
  have ht' : globalSectionsUpperStarMap A m F =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op ≫ tG.inv.app K := by
    apply (cancel_mono (tG.hom.app K)).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact ht
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← hn]
  exact hz.symm


private theorem chart_pullback_iso
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (U : Y.Etale) :
    let _W := f.Etale.obj U
    let W' := f'.Etale.obj (g.Etale.obj U)
    let t := baseChangeSectionMap sq (W := U) (V := g.Etale.obj U)
      (pullback.fst U.hom g)
      (pullback.condition (f := U.hom) (g := g))
    IsIso (pullback.lift t W'.hom (baseChangeSectionMap_snd sq _ _)) := by
  intro _W W' t
  let p := pullback.snd U.hom f
  let q := pullback.snd U.hom g
  let p' := pullback.snd q f'
  let t₀ : pullback q f' ⟶ pullback U.hom f := t
  have ht₁ : t₀ ≫ pullback.fst U.hom f =
      pullback.fst q f' ≫ pullback.fst U.hom g :=
    baseChangeSectionMap_fst sq _ _
  have ht₂ : t₀ ≫ p = p' ≫ g' := baseChangeSectionMap_snd sq _ _
  let i := pullback.lift t₀ p' ht₂
  let k : pullback p g' ⟶ pullback U.hom g :=
    pullback.lift (pullback.fst p g' ≫ pullback.fst U.hom f)
      (pullback.snd p g' ≫ f') (by
        calc
          _ = pullback.fst p g' ≫ p ≫ f := by
            rw [Category.assoc, pullback.condition]
          _ = pullback.snd p g' ≫ g' ≫ f := by
            rw [← Category.assoc, pullback.condition, Category.assoc]
          _ = _ := by rw [sq.w, Category.assoc])
  have hk₂ : k ≫ q = pullback.snd p g' ≫ f' := pullback.lift_snd _ _ _
  let j : pullback p g' ⟶ pullback q f' :=
    pullback.lift k (pullback.snd p g') hk₂
  have hi₁ : i ≫ pullback.fst p g' = t₀ := pullback.lift_fst _ _ _
  have hi₂ : i ≫ pullback.snd p g' = p' := pullback.lift_snd _ _ _
  have hj₁ : j ≫ pullback.fst q f' = k := pullback.lift_fst _ _ _
  have hj₂ : j ≫ p' = pullback.snd p g' := pullback.lift_snd _ _ _
  have hk₁ : k ≫ pullback.fst U.hom g =
      pullback.fst p g' ≫ pullback.fst U.hom f := pullback.lift_fst _ _ _
  change IsIso i
  refine ⟨⟨j, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp]
        erw [reassoc_of% hj₁]
        change i ≫ k ≫ pullback.fst U.hom g =
          pullback.fst q f' ≫ pullback.fst U.hom g
        erw [hk₁, ← Category.assoc, hi₁, ht₁]
      · simp only [Category.assoc, Category.id_comp]
        erw [reassoc_of% hj₁]
        change i ≫ k ≫ q = pullback.fst q f' ≫ q
        erw [hk₂, ← Category.assoc, hi₂]
        exact (pullback.condition (f := q) (g := f')).symm
    · simp only [Category.assoc, Category.id_comp]
      change i ≫ j ≫ p' = p'
      erw [hj₂, hi₂]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp]
        erw [reassoc_of% hi₁]
        change j ≫ t₀ ≫ pullback.fst U.hom f =
          pullback.fst p g' ≫ pullback.fst U.hom f
        erw [ht₁, ← Category.assoc, hj₁, hk₁]
      · simp only [Category.assoc, Category.id_comp]
        erw [reassoc_of% hi₁]
        change j ≫ t₀ ≫ p = pullback.fst p g' ≫ p
        erw [ht₂, ← Category.assoc, hj₂]
        exact (pullback.condition (f := p) (g := g')).symm
    · simp only [Category.assoc, Category.id_comp]
      erw [hi₂, hj₂]


private theorem chartSections_pullback_square
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (U : Y.Etale)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ((g')^*[AddCommGrpCat.{u + 1}]).obj G ⟶ G') :
    let W := f.Etale.obj U
    let W' := f'.Etale.obj (g.Etale.obj U)
    let t : W'.left ⟶ W.left := baseChangeSectionMap sq (W := U) (V := g.Etale.obj U)
      (pullback.fst U.hom g)
      (pullback.condition (f := U.hom) (g := g))
    (sectionsIso W G).inv ≫
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t
          ((upperStar AddCommGrpCat.{u + 1} (Z := W.left) (Y := X) W.hom).obj G) ≫
        (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((chartRestrictionSquare g' W W' t (baseChangeSectionMap_snd sq _ _)).hom.app G ≫
            (upperStar AddCommGrpCat.{u + 1} (Z := W'.left) (Y := X') W'.hom).map ψ) ≫
        (sectionsIso W' G').hom =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit.app G).hom.app (op W) ≫
        (((g')^*[AddCommGrpCat.{u + 1}]).obj G).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift t W'.hom (baseChangeSectionMap_snd sq _ _))
            (pullback.lift_snd _ _ _)).op ≫ ψ.hom.app (op W') := by
  intro W W' t
  let i := pullback.lift t W'.hom (baseChangeSectionMap_snd sq _ _)
  let _ : IsIso i := chart_pullback_iso sq U
  have h := etaleObjectSections_pullback g' W W' t (baseChangeSectionMap_snd sq _ _)
    i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) G
  have hn := (etaleObjectSectionsIso W').hom.naturality ψ
  rw [sectionsIso_inv_eq]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% h, ← reassoc_of% hn]
  rw [← sectionsIso_inv_eq]
  erw [Iso.inv_hom_id]
  simp only [Category.comp_id]
  rfl

set_option maxRecDepth 2048 in
private theorem chartGenerator_pullback
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (U : Y.Etale) :
    let W := f.Etale.obj U
    let W' := f'.Etale.obj (g.Etale.obj U)
    let t : W'.left ⟶ W.left := baseChangeSectionMap sq (W := U) (V := g.Etale.obj U)
      (pullback.fst U.hom g)
      (pullback.condition (f := U.hom) (g := g))
    let G := ((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)
    let e := commutativeExchangeRawSourceIso sq U
    (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t
        ((upperStar AddCommGrpCat.{u + 1} (Z := W.left) (Y := X) W.hom).obj G) ≫
      (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((chartRestrictionSquare g' W W' t (baseChangeSectionMap_snd sq _ _)).hom.app G ≫
          (upperStar AddCommGrpCat.{u + 1} (Z := W'.left) (Y := X') W'.hom).map e.hom))
      (generator f U) = generator f' (g.Etale.obj U) := by
  intro W W' t G e
  let A := (abelianComparisonFree Y).obj U
  let A' := (abelianComparisonFree Y').obj (g.Etale.obj U)
  let e₀ := abelianFreeRepresentablePullbackIso g U
  let x := freeRepresentableHomEquiv Y U A (𝟙 A)
  let x' := freeRepresentableHomEquiv Y' (g.Etale.obj U) A' (𝟙 A')
  have heval := free_pullback_sections g U A' A (𝟙 A) e₀.hom
  erw [(upperStar AddCommGrpCat.{u + 1} g).map_id] at heval
  dsimp only [e₀] at heval
  erw [Category.id_comp, Iso.inv_hom_id] at heval
  simp only [free_hom_evaluation, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app] at heval
  change x' = e₀.hom.hom.app (op (g.Etale.obj U))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app A).hom.app (op U) x)
      at heval
  have hmate : ((g)^*[AddCommGrpCat.{u + 1}]).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A) ≫
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app G ≫
      ((f')_*[AddCommGrpCat.{u + 1}]).map e.hom =
    e₀.hom ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').unit.app A' := by
    rw [← Category.assoc, map_unit_baseChangeMap_app]
    dsimp only [e, commutativeExchangeRawSourceIso, Iso.trans_hom,
      Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [Iso.hom_inv_id_app_assoc]
    exact ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').unit.naturality
      e₀.hom).symm
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A)
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hs := baseChangeMap_app_pullSection sq G (W := U) (V := g.Etale.obj U) (pullback.fst U.hom g)
    (pullback.condition (f := U.hom) (g := g))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A).hom.app (op U) x)
  have hid : homToPullback g (pullback.fst U.hom g)
      (pullback.condition (f := U.hom) (g := g)) = 𝟙 (g.Etale.obj U) := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift (pullback.fst U.hom g) (pullback.snd U.hom g) _ = 𝟙 _
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
      Category.id_comp]
  rw [pullSection, hid] at hs
  erw [CategoryTheory.Functor.map_id] at hs
  change ((baseChangeMap AddCommGrpCat.{u + 1} sq).app G).hom.app
    (op (g.Etale.obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _).hom.app
        (op U) (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A).hom.app
          (op U) x)) = _ at hs
  have hh := congrArg (fun k ↦ k.hom.app (op (g.Etale.obj U))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app A).hom.app
      (op U) x)) hmate
  have hh' := congrArg (fun k ↦ k.hom.app (op U) x) hn
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, lowerStar_map_hom_app] at hh hh'
  erw [← hh', hs, ← heval] at hh
  have hsections := chartSections_pullback_square sq U G _ e.hom
  have h := congrArg (fun k ↦ k
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app A).hom.app
      (op U) x)) hsections
  change (sectionsIso W' _).hom
    ((globalSectionsUpperStarMap AddCommGrpCat.{u + 1} t _ ≫
      (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map _)
        (generator f U)) = _ at h
  change _ = e.hom.hom.app (op W')
    (pullSection g' G (U := W) (V := W') t
      (baseChangeSectionMap_snd sq _ _) _) at h
  erw [hh] at h
  apply (ConcreteCategory.bijective_of_isIso (sectionsIso W' _).hom).1
  refine h.trans ?_
  dsimp only [generator]
  exact (Iso.inv_hom_id_apply (sectionsIso W' _)
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f').unit.app A').hom.app
      (op (g.Etale.obj U)) x')).symm



attribute [local irreducible] rawRestrictedCohomologyComparison
  upperStar rawAffineComplexPullback generator
  commutativeExchangeRawSourceIso Evaluation.shiftIso Evaluation.zeroIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Converting the derived-Hom presheaf presentation needs extra elaboration steps.
/-- Evaluation of a raw class commutes with the geometric map of etale charts.
This contains no direct-image exchange morphism and no higher-image class map.
Source: Stacks Project, Cohomology on Sites, Tags 0D6F and 07A6; Tag 03Q8.
(blueprint: lem-kun-commutative-exchange-evaluation-compatibility).

Proof: Let V = U times_Y X and V' = (U times_Y Y') times_Y' X',
with projections p,p' and induced map t : V' -> V. The square with horizontal
maps t,g' and vertical maps p',p is cartesian, by the universal property of
the two fibre products. Hence ordinary sections of p^*G pull back along t
to sections of p'^*g'^*G, with coefficient comparison
(upperStarComp t p)^-1 followed by upperStarComp p' g'. On the represented
source, the unit composition identities and the defining free-representable
pullback Hom equivalence identify the transported identity generator with
the generator at U times_Y Y'. Apply the natural derived section pullback,
the derived unit for t followed by its global-sections composition comparison,
to z. On a single source its zeroth-homology map is the ordinary section map
just computed. On the shifted single target its shift comparison gives H^q
of rawAffineComplexPullback followed by the single of the displayed coefficient
comparison. The exact square comparison on singles is the same coefficient
comparison. Naturality at z, cancellation of the source single isomorphism,
and evaluation at the identity generator give the equality below.
Nothing requires the original square to be cartesian, q to be positive,
or either chart to be nonempty. -/
theorem commutativeExchangeEvaluationCompatibility
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale) :
    let t := pullback.map (g.Etale.obj U).hom f' U.hom f
      (pullback.fst U.hom g) g' g
      (pullback.condition (f := U.hom) (g := g)).symm sq.w.symm
    let c : ((t)^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.snd U.hom f)^*[AddCommGrpCat.{u + 1}]).obj F) ⟶
        ((pullback.snd (g.Etale.obj U).hom f')^*[AddCommGrpCat.{u + 1}]).obj
          (((g')^*[AddCommGrpCat.{u + 1}]).obj F) :=
      (upperStarComp AddCommGrpCat.{u + 1} t (pullback.snd U.hom f)).inv.app F ≫
      (upperStarComp AddCommGrpCat.{u + 1} (pullback.snd (g.Etale.obj U).hom f') g'
        (t ≫ pullback.snd U.hom f) (pullback.lift_snd _ _ _)).hom.app F
    rawRestrictedCohomologyComparison f q F U ≫
      (rawAffineComplexPullback (q : ℤ) t
        ((CochainComplex.singleFunctor _ 0).obj
          (((pullback.snd U.hom f)^*[AddCommGrpCat.{u + 1}]).obj F)) ≫
      (cohomology AddCommGrpCat.{u + 1} (pullback (g.Etale.obj U).hom f') (q : ℤ)).map
        (DerivedCategory.Q.map
          ((((t)^*[AddCommGrpCat.{u + 1}]).mapCochainComplexSingleFunctor 0).hom.app _ ≫
            (CochainComplex.singleFunctor _ 0).map c))) =
      commutativeExchangeRawPullbackMap sq F q U ≫
        rawRestrictedCohomologyComparison f' q _ (g.Etale.obj U) := by
  intro t c
  have hg := chartGenerator_pullback sq U
  have h := chartEvaluation_hom g'
    (pullback.snd U.hom f) (pullback.snd (g.Etale.obj U).hom f') t
    (pullback.lift_snd _ _ _) F q
    (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U))
    (((f')^*[AddCommGrpCat.{u + 1}]).obj
      ((abelianComparisonFree Y').obj (g.Etale.obj U)))
    (commutativeExchangeRawSourceIso sq U)
    (generator f U) (generator f' (g.Etale.obj U)) hg
  have hk := chartCohomologyMap_eq g'
    (pullback.snd U.hom f) (pullback.snd (g.Etale.obj U).hom f') t
    (pullback.lift_snd _ _ _) F q
  dsimp only at h hk
  rw [hk] at h
  erw [← commutativeExchangeEvaluationHom_rawComparison f F q U,
    ← commutativeExchangeEvaluationHom_rawComparison f' (((g')^*[AddCommGrpCat.{u + 1}]).obj F) q
      (g.Etale.obj U)] at h
  simpa only [c, commutativeExchangeRawPullbackMap, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app] using h

end AlgebraicGeometry.Etale
