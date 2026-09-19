/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Functoriality of `mapCochainComplexSingleFunctor`

For an exact functor `F : C ⥤ D` between abelian categories,
`CategoryTheory.Functor.mapCochainComplexSingleFunctor` is the isomorphism identifying
`F.mapHomologicalComplex (ComplexShape.up ℤ)` applied to a complex concentrated in a
single degree with the complex concentrated in that degree attached to the image by `F`.
This file records that this isomorphism is functorial in `F`: it is compatible with the
identity functor (`mapCochainComplexSingleFunctor_id`), with the composition of two
functors (`mapCochainComplexSingleFunctor_comp`) and with an isomorphism of functors
(`mapCochainComplexSingleFunctor_natIso`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]

lemma mapCochainComplexSingleFunctor_id (n : ℤ) :
    (𝟭 C).mapCochainComplexSingleFunctor n =
      isoWhiskerLeft (CochainComplex.singleFunctor C n)
        (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)) := by
  apply Iso.ext
  ext X i
  by_cases h : i = n
  · subst h
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.mapCochainComplexSingleFunctor]
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_tgt

lemma mapCochainComplexSingleFunctor_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) :
    (F ⋙ G).mapCochainComplexSingleFunctor n =
      isoWhiskerLeft (CochainComplex.singleFunctor C n)
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
            (ComplexShape.up ℤ)).symm ≪≫
        isoWhiskerRight (F.mapCochainComplexSingleFunctor n)
          (G.mapHomologicalComplex (ComplexShape.up ℤ)) ≪≫
        isoWhiskerLeft F (G.mapCochainComplexSingleFunctor n) := by
  apply Iso.ext
  ext X i
  by_cases h : i = n
  · subst h
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplex_map_f, Iso.refl_inv, NatTrans.id_app,
      Functor.map_comp, assoc, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Iso.symm_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom]
    erw [id_comp]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_tgt

lemma mapCochainComplexSingleFunctor_natIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ≅ G) (n : ℤ) :
    G.mapCochainComplexSingleFunctor n =
      isoWhiskerLeft (CochainComplex.singleFunctor C n)
          (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).symm ≪≫
        F.mapCochainComplexSingleFunctor n ≪≫
        isoWhiskerRight α (CochainComplex.singleFunctor D n) := by
  apply Iso.ext
  ext X i
  by_cases h : i = n
  · subst h
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.mapCochainComplexSingleFunctor, HomologicalComplex.single_map_f_self]
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_tgt

end CategoryTheory.Functor
