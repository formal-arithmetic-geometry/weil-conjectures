/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorModel

/-! # The ordinary scalar tensor square on homotopy categories

Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.5.9(5), p. 51;
explicit comparison of the ordinary tensor and single-complex constructions.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option autoImplicit false

universe v u u'
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResidueOrdinaryTensorNormalization
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace CategoryTheory
variable {C : Type u} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C]
  {D : Type u'} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] [F.Monoidal]
private theorem single_inv_quotient (B : C) (K : CochainComplex C ℤ) :
    (homotopyTensorSingleIso B).inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
    ((tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)).inv.app K ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B).inv.app K) ≫
      Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ))
        ((HomologicalComplex.single C (.up ℤ) 0).obj B) K := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj B
  let e : tensorLeft P ≅ (tensorLeft B).mapHomologicalComplex (.up ℤ) :=
    CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B
  let pre := (Functor.Monoidal.commTensorLeft q P).symm ≪≫
    Functor.isoWhiskerRight e q ≪≫ (tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)
  have h : Functor.whiskerLeft q (homotopyTensorSingleIso B).inv = pre.inv := by
    unfold homotopyTensorSingleIso
    exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ _).obj q)).map_preimage _
  have ha := NatTrans.congr_app h K
  simpa only [pre, e, q, P, Functor.whiskerLeft_app, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.Monoidal.commTensorLeft_hom_app, Category.assoc] using ha

private theorem tensor_single_complex_iso (B : C) (B' : D) (e : F.obj B ≅ B')
    (K : CochainComplex C ℤ) :
    let τ : tensorLeft B ⋙ F ⟶ F ⋙ tensorLeft B' :=
      (Functor.Monoidal.commTensorLeft F B).inv ≫
        Functor.whiskerLeft F ((curriedTensor D).map e.hom)
    (F.mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B).inv.app K) ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj B)).app K ≫
      ((F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (HomologicalComplex.single D (.up ℤ) 0).map e.hom) ▷
        (F.mapHomologicalComplex (.up ℤ)).obj K =
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ≫
      (CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor D)
        B').inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  dsimp only
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  simp only [CochainComplex.map₂HomologicalComplexObjSingleIso_inv_app,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison, Functor.map_comp, Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight]
  simp only [comp_whiskerRight, HomologicalComplex.comp_f, Category.assoc]
  change F.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ▷ K.X n) ≫
    Functor.OplaxMonoidal.δ F _ (K.X n) ≫
    ((F.mapCochainComplexSingleFunctor 0).hom.app B).f 0 ▷ F.obj (K.X n) ≫
    ((HomologicalComplex.single D (.up ℤ) 0).map e.hom).f 0 ▷ F.obj (K.X n) ≫ _ = _
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp only [Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    Functor.Monoidal.commTensorLeft_inv_app,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [comp_whiskerRight, Category.assoc]
  rfl

private theorem tensor_single_homotopy_iso (B : C) (B' : D) (e : F.obj B ≅ B')
    (P : HomotopyCategory C (.up ℤ)) :
    let τ : tensorLeft B ⋙ F ⟶ F ⋙ tensorLeft B' :=
      (Functor.Monoidal.commTensorLeft F B).inv ≫
        Functor.whiskerLeft F ((curriedTensor D).map e.hom)
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
        Functor.tensorModelCoefficient B' :=
      (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app P ≫
      (homotopyTensorSingleIso B').inv.app FP =
    (F.mapHomotopyCategory (.up ℤ)).map ((homotopyTensorSingleIso B).inv.app P) ≫
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
        (Functor.tensorModelCoefficient B)).app P ≫ eH.hom ▷ FP := by
  dsimp only
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  let q := HomotopyCategory.quotient D (.up ℤ)
  have h := tensor_single_complex_iso F B B' e K
  dsimp only at h
  have hB := single_inv_quotient B K
  have hB' := single_inv_quotient B' FK
  simp only [NatTrans.mapHomotopyCategory_app]
  erw [hB, hB']
  have hfac (L : CochainComplex C ℤ) :
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app L = 𝟙 _ := rfl
  have hfacB : ((tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have hfacB' : ((tensorLeft B').mapHomotopyCategoryFactors (.up ℤ)).inv.app FK = 𝟙 _ := rfl
  have hμB : Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ))
      ((HomologicalComplex.single C (.up ℤ) 0).obj B) K = 𝟙 _ := rfl
  have hμB' : Functor.LaxMonoidal.μ q
      ((HomologicalComplex.single D (.up ℤ) 0).obj B') FK = 𝟙 _ := rfl
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, hfac, hfacB, hfacB',
    hμB, Category.id_comp,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
  dsimp only [q] at hμB'
  erw [hμB', Category.comp_id, Category.comp_id, Category.id_comp]
  simp only [Functor.mapHomotopyCategory_map]
  have hq := q.congr_map h.symm
  simp only [Functor.map_comp] at hq
  have hqw : q.map
      (((F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (HomologicalComplex.single D (.up ℤ) 0).map e.hom) ▷ FK) =
      q.map ((F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (HomologicalComplex.single D (.up ℤ) 0).map e.hom) ▷ q.obj FK := by
    rw [Functor.Monoidal.map_whiskerRight]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [hqw] at hq
  exact hq

private theorem tensor_single_homotopy_iso_inv (B : C) (B' : D) (e : F.obj B ≅ B')
    (P : HomotopyCategory C (.up ℤ)) :
    let τ : tensorLeft B ⋙ F ⟶ F ⋙ tensorLeft B' :=
      (Functor.Monoidal.commTensorLeft F B).inv ≫
        Functor.whiskerLeft F ((curriedTensor D).map e.hom)
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
        Functor.tensorModelCoefficient B' :=
      (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    (NatTrans.mapHomotopyCategory τ (.up ℤ)).app P ≫
      (homotopyTensorSingleIso B').inv.app FP ≫ eH.inv ▷ FP =
    (F.mapHomotopyCategory (.up ℤ)).map ((homotopyTensorSingleIso B).inv.app P) ≫
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
        (Functor.tensorModelCoefficient B)).app P := by
  dsimp only
  have h := tensor_single_homotopy_iso F B B' e P
  dsimp only at h
  erw [reassoc_of% h]
  conv_lhs =>
    rhs; rhs
    erw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  erw [Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] residueOrdinaryUpperStarMonoidal

set_option maxHeartbeats 900000 in
-- The degreewise calculation compares several concrete module-functor composites.
/-- The scalar tensor square agrees with ordinary pullback's comonoidal map.
Source: Bhatt--Scholze, Remark 6.8.15 and Lemma 6.5.9(5), p. 51.
(auxiliary; not a blueprint node)

Proof. Use the balanced coequalizer presentation of extension of scalars to
identify restriction after extension with tensoring by the restricted regular
module. Precompose the comparison with the coequalizer epimorphism. The two
maps then apply pullback to the coefficient and the module, followed by their
scalar action. Naturality of the coefficient map identifies the balancing
relations. The inverse monoidal unit in the coefficient isomorphism cancels
the pulled-back regular module. Faithfulness of the forgetful functor gives
the ordinary module equality. Apply this equality in every degree of a complex;
naturality makes it commute with the differentials. The single tensor
comparison and its naturality then give the asserted homotopy equality.
This uses neither derived categories nor flatness. -/
theorem residueOrdinaryTensorPull_homotopy
    (Λ A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
      (.up ℤ)) :
    let F := (f)^*⟦Λ⟧
    let TY := Mod.extendScalars (coefficientMap φ Y)
    let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap φ X)
    let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (coefficientMap φ Y)
    let B := SY.obj (Mod.regular (condensedRingObj A Y))
    let B' := SX.obj (Mod.regular (condensedRingObj A X))
    let FP := (F.mapHomotopyCategory (.up ℤ)).obj P
    let TP := (TY.mapHomotopyCategory (.up ℤ)).obj P
    let _ := residueOrdinaryUpperStarMonoidal Λ f
    let e : F.obj B ≅ B' :=
      residueOrdinaryRestrictedRegularPullIso Λ A φ f
    let eH : (F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ≅
        Functor.tensorModelCoefficient B' :=
      (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj B) ≪≫
      (HomotopyCategory.quotient _ (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single _ (.up ℤ) 0).mapIso e)
    (NatTrans.mapHomotopyCategory (comapUpperStarIso φ f).inv (.up ℤ)).app TP ≫
      (SX.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (pullIso φ f).inv (.up ℤ)).app P) ≫
      (Mod.tensorPresentationHomotopyIso (coefficientMap φ X)).hom.app FP ≫
      (homotopyTensorSingleIso B').inv.app FP ≫ eH.inv ▷ FP =
    (F.mapHomotopyCategory (.up ℤ)).map
        ((Mod.tensorPresentationHomotopyIso (coefficientMap φ Y)).hom.app P ≫
          (homotopyTensorSingleIso B).inv.app P) ≫
      ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
        (Functor.tensorModelCoefficient B)).app P := by
  dsimp only
  let F := (f)^*⟦Λ⟧
  let TY := Mod.extendScalars (coefficientMap φ Y)
  let SX := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap φ X)
  let SY := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap φ Y)
  let B := SY.obj (Mod.regular (condensedRingObj A Y))
  let B' := SX.obj (Mod.regular (condensedRingObj A X))
  let e := residueOrdinaryRestrictedRegularPullIso Λ A φ f
  let _ := residueOrdinaryUpperStarMonoidal Λ f
  let τ : tensorLeft B ⋙ F ⟶ F ⋙ tensorLeft B' :=
    (Functor.Monoidal.commTensorLeft F B).inv ≫
      Functor.whiskerLeft F ((curriedTensor _).map e.hom)
  have hm :
      (NatTrans.mapHomotopyCategory (comapUpperStarIso φ f).inv (.up ℤ)).app
          ((TY.mapHomotopyCategory (.up ℤ)).obj P) ≫
        (SX.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (pullIso φ f).inv (.up ℤ)).app P) ≫
        (Mod.tensorPresentationHomotopyIso (coefficientMap φ X)).hom.app
          ((F.mapHomotopyCategory (.up ℤ)).obj P) =
      (F.mapHomotopyCategory (.up ℤ)).map
          ((Mod.tensorPresentationHomotopyIso (coefficientMap φ Y)).hom.app P) ≫
        (NatTrans.mapHomotopyCategory τ (.up ℤ)).app P := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    dsimp only [Mod.tensorPresentationHomotopyIso]
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    congr 1
    ext n : 1
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f]
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.Monoidal.commTensorLeft_inv_app]
    exact residueOrdinaryTensorPull_module Λ A φ f (K.X n)
  have ht := tensor_single_homotopy_iso_inv F B B' e P
  dsimp only at ht
  erw [reassoc_of% hm, ht]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
