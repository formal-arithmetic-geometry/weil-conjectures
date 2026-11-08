/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical H-zero comparison and its flat-model transport

Source: Stacks Project, Tag 06YH, derived tensor and its comparison to ordinary tensor.
-/

@[expose] public section

universe w v u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{w} C]

noncomputable section

/-- The total tensor of the two degree-zero complexes is the ordinary tensor in degree zero.
This uses the tensor/single comparison followed by the termwise functor/single comparison. -/
def moduleCup_singleTensorIso (F G : C) :
    (CochainComplex.singleFunctor C 0).obj F ⊗
      (CochainComplex.singleFunctor C 0).obj G ≅
        (CochainComplex.singleFunctor C 0).obj (F ⊗ G) :=
  (CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor C) G).app
      ((CochainComplex.singleFunctor C 0).obj F) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorRight G) (.up ℤ) 0).app F

private lemma flat_comparison (P L : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    (QObjTensorQObjIsoOfKFlatLeft P L hP).hom = Functor.LaxMonoidal.μ Q P L := by
  simp only [QObjTensorQObjIsoOfKFlatLeft, Iso.trans_hom, tensorIso_hom,
    Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom]
  change _ = ((quotientCompQhIso C).inv.app P ⊗ₘ
    (quotientCompQhIso C).inv.app L) ≫
    (Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj L) ≫
      Qh.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) P L)) ≫
    (quotientCompQhIso C).hom.app (P ⊗ L)
  simp only [Category.assoc, Functor.Monoidal.μIso_hom]
  rfl

private lemma transport (F G : C) (P : CochainComplex C ℤ)
    (p : P ⟶ (CochainComplex.singleFunctor C 0).obj F) [QuasiIso p]
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    Functor.LaxMonoidal.μ Q ((CochainComplex.singleFunctor C 0).obj F)
        ((CochainComplex.singleFunctor C 0).obj G) ≫
      Q.map (moduleCup_singleTensorIso F G).hom =
    (tensorIso (asIso (Q.map p))
      (Iso.refl (Q.obj ((CochainComplex.singleFunctor C 0).obj G)))).inv ≫
    (QObjTensorQObjIsoOfKFlatLeft P ((CochainComplex.singleFunctor C 0).obj G) hP).hom ≫
    Q.map (p ⊗ₘ 𝟙 _) ≫ Q.map (moduleCup_singleTensorIso F G).hom := by
  rw [flat_comparison]
  rw [← cancel_epi (tensorIso (asIso (Q.map p))
    (Iso.refl (Q.obj ((CochainComplex.singleFunctor C 0).obj G)))).hom]
  rw [Iso.hom_inv_id_assoc]
  simp only [tensorIso_hom, asIso_hom, Iso.refl_hom, tensorHom_id]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]

end
end DerivedCategory
