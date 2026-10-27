/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Exact natural transformations on the single-degree models. -/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SheafProject

/-- A localized natural transformation, transported through the canonical exact/single
comparisons, is the single of its ordinary component.

Source: localization of natural transformations and the single-complex comparison in
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor.
(blueprint: lem-pur-exact-single-transformation)

Proof: the localization component at a cochain single is the conjugate of the
cochain natural transformation by mapDerivedCategoryFactors. Unfold the canonical
single comparisons and cancel the target factors. Combine the two Q maps on each
side. The resulting identity of cochain maps is checked in the support degree by
the definitions of singleMapHomologicalComplex and singleObjXSelf; in every other
degree the target is zero. -/
theorem exactSingle_transformation
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (n : ℤ) (X : A) :
    (Localization.liftNatTrans _root_.DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) _ _
      F.mapDerivedCategory G.mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (.up ℤ))
        _root_.DerivedCategory.Q)).app
        ((_root_.DerivedCategory.singleFunctor A n).obj X) ≫
      (G.mapDerivedCategorySingleFunctor n).hom.app X =
    (F.mapDerivedCategorySingleFunctor n).hom.app X ≫
      (_root_.DerivedCategory.singleFunctor B n).map (α.app X) := by
  let K := (CochainComplex.singleFunctor A n).obj X
  erw [Localization.liftNatTrans_app _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (.up ℤ))
      _root_.DerivedCategory.Q) K]
  simp only [Localization.Lifting.iso, Functor.mapDerivedCategorySingleFunctor,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    _root_.DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  erw [G.mapDerivedCategory.map_id, F.mapDerivedCategory.map_id]
  dsimp only [K, _root_.DerivedCategory.singleFunctor, _root_.DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctors, SingleFunctors.postcomp, Functor.comp_obj,
    _root_.DerivedCategory.Q, Functor.comp_map]
  simp only [Category.id_comp]
  rw [Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id, Category.id_comp]
  change F.mapDerivedCategoryFactors.hom.app K ≫
      _root_.DerivedCategory.Q.map _ ≫ _root_.DerivedCategory.Q.map _ =
    F.mapDerivedCategoryFactors.hom.app K ≫
      _root_.DerivedCategory.Q.map _ ≫ _root_.DerivedCategory.Q.map _
  rw [← _root_.DerivedCategory.Q.map_comp, ← _root_.DerivedCategory.Q.map_comp]
  apply congrArg (fun f ↦ F.mapDerivedCategoryFactors.hom.app K ≫
    _root_.DerivedCategory.Q.map f)
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = n
  · subst i
    simp [K, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n _ i hi).eq_of_tgt _ _

end SheafProject
