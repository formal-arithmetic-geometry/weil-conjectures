/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Bounded below right derived functors on complexes concentrated in one degree

Let `F : C ⥤ D` be an additive functor between abelian categories, `C` having enough
injectives. This file compares `R⁺F` on the complex `X[0]` concentrated in degree `0` with
the complex `(F X)[0]`.

- `CategoryTheory.Functor.mapHomotopyCategoryPlusSingleFunctor`: the single functors to the
  bounded below homotopy categories commute with `F.mapHomotopyCategoryPlus`.
- `CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorPlusUnit`: the natural
  transformation `(F X)[0] ⟶ R⁺F (X[0])` induced by the unit of `R⁺F`; it is an isomorphism
  when `X` is injective, `X[0]` being then a bounded below complex of injectives.
- `CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor`: for
  an injective `X`, the cohomology of `R⁺F (X[0])` vanishes outside degree `0`.
- `CategoryTheory.Functor.retractSingleFunctorRightDerivedFunctorPlus`: a criterion for `X[0]`
  to be a retract of `R⁺F (Y[0])`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- The single functors to the bounded below homotopy categories commute with the functor
`F.mapHomotopyCategoryPlus` induced by an additive functor `F`. -/
noncomputable def Functor.mapHomotopyCategoryPlusSingleFunctor (F : C ⥤ D) [F.Additive]
    (n : ℤ) :
    HomotopyCategory.Plus.singleFunctor C n ⋙ F.mapHomotopyCategoryPlus ≅
      F ⋙ HomotopyCategory.Plus.singleFunctor D n :=
  ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight C).preimageIso
    (Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso C n)
        (F.mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F
        (ComplexShape.up ℤ) n) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (HomotopyCategory.singleFunctorPostcompQuotientIso D n).symm)

/-- The single functors of the bounded below derived category are induced by those of the
bounded below homotopy category. -/
noncomputable def DerivedCategory.Plus.singleFunctorIsoCompQh [HasDerivedCategory C] (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ≅
      HomotopyCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Qh :=
  Iso.refl _

/-- The complex `X[0]` attached to an injective object `X` consists of injective objects. -/
instance HomotopyCategory.Plus.injective_singleFunctor_obj_X (X : C) [Injective X] (n : ℤ) :
    Injective (((HomotopyCategory.Plus.singleFunctor C 0).obj X).obj.as.X n) := by
  by_cases hn : n = 0
  · subst hn
    exact Injective.of_iso (HomologicalComplex.singleObjXSelf _ 0 X).symm inferInstance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 X n hn).injective

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The natural transformation `(F X)[0] ⟶ R⁺F (X[0])` induced by the unit
`F.mapHomotopyCategoryPlus ⋙ Qh ⟶ Qh ⋙ R⁺F` of the bounded below right derived functor. -/
noncomputable def Functor.singleFunctorCompRightDerivedFunctorPlusUnit (F : C ⥤ D)
    [F.Additive] :
    F ⋙ DerivedCategory.Plus.singleFunctor D 0 ⟶
      DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus :=
  Functor.whiskerLeft F (DerivedCategory.Plus.singleFunctorIsoCompQh 0).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryPlusSingleFunctor 0).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C 0)
      F.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.Plus.singleFunctorIsoCompQh 0).inv
      F.rightDerivedFunctorPlus

/-- On an injective object `X`, the comparison `(F X)[0] ⟶ R⁺F (X[0])` is an isomorphism, the
unit of `R⁺F` being an isomorphism on bounded below complexes of injectives. -/
instance Functor.isIso_singleFunctorCompRightDerivedFunctorPlusUnit_app (F : C ⥤ D)
    [F.Additive] (X : C) [Injective X] :
    IsIso (F.singleFunctorCompRightDerivedFunctorPlusUnit.app X) := by
  dsimp [Functor.singleFunctorCompRightDerivedFunctorPlusUnit]
  infer_instance

/-- For an injective object `X`, the cohomology of `R⁺F (X[0])` vanishes outside degree `0`. -/
lemma Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor (F : C ⥤ D)
    [F.Additive] (X : C) [Injective X] {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (asIso (F.singleFunctorCompRightDerivedFunctorPlusUnit.app X)).symm)
  rcases hq.lt_or_gt with hq | hq
  · exact DerivedCategory.Plus.isZero_homology_of_isGE
      ((DerivedCategory.Plus.singleFunctor D 0).obj (F.obj X)) 0 q hq
  · exact DerivedCategory.Plus.isZero_homology_of_isLE
      ((DerivedCategory.Plus.singleFunctor D 0).obj (F.obj X)) 0 q hq

/-- Let `u : X ⟶ F Y`, `m : Y ⟶ J` with `J` injective and `r : F J ⟶ X` be such that
`u ≫ F m ≫ r = 𝟙 X`. Then `X[0]` is a retract of `R⁺F (Y[0])`: the section is `u[0]` followed
by the comparison `(F Y)[0] ⟶ R⁺F (Y[0])`, the retraction is `R⁺F (m[0])` followed by the
inverse of the comparison `(F J)[0] ≅ R⁺F (J[0])` and by `r[0]`. -/
noncomputable def Functor.retractSingleFunctorRightDerivedFunctorPlus (F : C ⥤ D)
    [F.Additive] {X : D} {Y J : C} [Injective J] (u : X ⟶ F.obj Y) (m : Y ⟶ J)
    (r : F.obj J ⟶ X) (h : u ≫ F.map m ≫ r = 𝟙 X) :
    Retract ((DerivedCategory.Plus.singleFunctor D 0).obj X)
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj Y)) where
  i := (DerivedCategory.Plus.singleFunctor D 0).map u ≫
    F.singleFunctorCompRightDerivedFunctorPlusUnit.app Y
  r := F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map m) ≫
    (asIso (F.singleFunctorCompRightDerivedFunctorPlusUnit.app J)).inv ≫
    (DerivedCategory.Plus.singleFunctor D 0).map r
  retract := by
    have hnat := F.singleFunctorCompRightDerivedFunctorPlusUnit.naturality m
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    rw [assoc, ← reassoc_of% hnat, asIso_inv, IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp, assoc, h, Functor.map_id]

end CategoryTheory
