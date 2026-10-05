/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Notation for the right derived functor on the bounded below derived category

We introduce the notation `R+(F)` for
`CategoryTheory.Functor.rightDerivedFunctorPlus F`, the right derived functor
`DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` of an additive functor `F : C ⥤ D`
between abelian categories, where `C` has enough injectives.

We also show that the higher right derived functors vanish on injective objects
(`CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor`).
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

@[inherit_doc rightDerivedFunctorPlus]
scoped notation "R+(" F ")" => rightDerivedFunctorPlus F

end Functor

end CategoryTheory

open CategoryTheory Limits

/-- For an additive functor `F` out of an abelian category with enough injectives and an
injective object `I`, the higher right derived functors of `F` vanish on `I`: the degree-`q`
homology of `R⁺F(I[0])` is zero for `q ≠ 0`. -/
theorem CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (I : C) [Injective I] {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj I))) := by
  let K : CochainComplex.Plus C := ⟨(CochainComplex.singleFunctor C 0).obj I, ⟨0, inferInstance⟩⟩
  have (n : ℤ) : Injective (((HomotopyCategory.Plus.quotient C).obj K).obj.as.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).injective
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K))).symm)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactorsh D q).app _)
  refine IsZero.of_iso ?_ ((HomotopyCategory.homologyFunctorFactors D _ q).app _)
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  exact Functor.map_isZero F (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
