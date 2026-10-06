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

We also record that the right derived functor of `F` sends an injective object `I` placed
in a single degree `n` to `F.obj I` placed in degree `n`
(`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleFunctorIso`): an injective object
is its own injective resolution.

We also show that the higher right derived functors vanish on injective objects
(`CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor`), and
that the right derived functor preserves the property of being cohomologically `≥ n`
(`CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor

@[inherit_doc rightDerivedFunctorPlus]
scoped notation "R+(" F ")" => rightDerivedFunctorPlus F

variable {C₀ C D : Type*} [Category* C₀] [Category* C] [Category* D] [Preadditive C₀]
  [HasZeroObject C₀] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]

/-- For an additive functor `G : C₀ ⥤ D`, the image in `DerivedCategory.Plus D` of the
single complex `X[n]` under `G.mapHomotopyCategoryPlus` is the single complex `(G.obj X)[n]`. -/
noncomputable def mapHomotopyCategoryPlusSingleFunctorQhObjIso (G : C₀ ⥤ D) [G.Additive]
    (n : ℤ) (X : C₀) :
    DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor C₀ n).obj X)) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (G.obj X) :=
  DerivedCategory.Plus.ι.preimageIso
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex G _ n).app X))

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor of `F` sends an injective object `I` placed in degree `n` to
`F.obj I` placed in degree `n`: the single complex `I[n]` is a bounded below complex of
injective objects, on which the unit of the right derived functor is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIso (n : ℤ) (I : C) [Injective I] :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj I) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (F.obj I) :=
  F.rightDerivedFunctorPlus.mapIso (mapHomotopyCategoryPlusSingleFunctorQhObjIso
      (InjectiveObject.ι C) n ⟨I, inferInstance⟩).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor (InjectiveObject C) n).obj
        ⟨I, inferInstance⟩)))).symm ≪≫
    (mapHomotopyCategoryPlusSingleFunctorQhObjIso (InjectiveObject.ι C ⋙ F) n
      ⟨I, inferInstance⟩ :)

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

/-- For an additive functor `F` out of an abelian category with enough injectives, the right
derived functor `R⁺F` preserves the property of being cohomologically `≥ n`: if `K` has no
homology in degrees `< n`, neither has `R⁺F(K)`, since `K` is represented by a complex of
injective objects concentrated in degrees `≥ n`. -/
theorem CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (K : DerivedCategory.Plus C) (n : ℤ) [K.IsGE n] {q : ℤ}
    (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj (F.rightDerivedFunctorPlus.obj K)) := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let M := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (F.rightDerivedFunctorPlus.mapIso e.symm))
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj M))).symm)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactorsh D q).app _)
  refine IsZero.of_iso ?_ ((HomotopyCategory.homologyFunctorFactors D _ q).app _)
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  change IsZero (F.obj ((InjectiveObject.ι C).obj (L.obj.X q)))
  exact F.map_isZero ((InjectiveObject.ι C).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE L.obj n q hq))
