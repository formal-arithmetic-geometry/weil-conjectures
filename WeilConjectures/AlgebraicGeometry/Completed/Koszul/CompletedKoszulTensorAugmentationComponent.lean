/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitZeroIso

/-! # The component normalization square for completed Koszul tensor augmentation

Source: Stacks Project, proetale.tex, Tag 099M, proof of lemma-naive-completion;
sites-cohomology.tex, Tag 06YN, the total tensor construction.
(blueprint: lem-weil-pbc-completed-koszul-tensor-augmentation-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] completedAdicRing

@[reassoc] private lemma unitTensorInv_f
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (CompletedAdicModules T d) ℤ) (p : ℤ) :
    (λ_ K).inv.f p = (λ_ (K.X p)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).inv ▷ K.X p ≫
      HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) := by
  exact HomologicalComplex.leftUnitor'_inv K p

@[reassoc] private lemma unitTensor_ι_hom
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K : CochainComplex (CompletedAdicModules T d) ℤ) (p : ℤ) :
    HomologicalComplex.ιTensorObj (𝟙_ _) K 0 p p (zero_add p) ≫
        (λ_ K).hom.f p =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (CompletedAdicModules T d))).hom ▷ K.X p ≫ (λ_ (K.X p)).hom := by
  apply (cancel_epi ((λ_ (K.X p)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (CompletedAdicModules T d))).inv ▷ K.X p)).1
  simp only [Category.assoc]
  erw [← unitTensorInv_f_assoc T d,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

@[reassoc] private lemma tensorSummand_whiskerLeft
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (P K L : CochainComplex (CompletedAdicModules T d) ℤ) (c : K ⟶ L)
    (p q k : ℤ) (h : p + q = k) :
    HomologicalComplex.ιTensorObj P K p q k h ≫ (P ◁ c).f k =
      P.X p ◁ c.f q ≫ HomologicalComplex.ιTensorObj P L p q k h := by
  change _ ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P) c
    (curriedTensor _) (.up ℤ)).f k = _
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map]
  exact Category.id_comp _

end AlgebraicGeometry.Scheme
