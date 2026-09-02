/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The bounded below derived adjunction of an adjunction with exact left adjoint

Let `L ⊣ R` be an adjunction of additive functors between abelian categories, with `L`
exact and the target of `L` having enough injectives. Then `L` induces a functor
`L.mapDerivedCategoryPlus` on the bounded below derived categories by applying it
levelwise, `R` has a bounded below right derived functor `R.rightDerivedFunctorPlus`, and
we show that these two are again adjoint. In particular the adjunction has a unit

`𝟭 ⟶ L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus`,

which is what the comparison of derived lower shrieks along a refinement of
compactifications is built from.

## Main definitions

- `CategoryTheory.Adjunction.derivedPlus`: the adjunction
  `L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus`.
- `CategoryTheory.Adjunction.derivedPlus_unit_app_fac` and
  `CategoryTheory.Adjunction.derivedPlus_unit_eq`: the formula computing the unit on the
  image of a bounded below complex, and the fact that this formula characterises it.

## The proof

The construction is Mathlib's `CategoryTheory.Adjunction.derived`, which produces an
adjunction between a left derived functor and a right derived functor as soon as the two
composites are again derived functors ("absoluteness"), applied to the adjunction
`L.mapHomotopyCategoryPlus ⊣ R.mapHomotopyCategoryPlus` on the bounded below homotopy
categories. There are two absoluteness statements to check, and they are of a different
nature:

* `L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus` is the left derived functor of
  `L.mapHomotopyCategoryPlus ⋙ Qh ⋙ R.rightDerivedFunctorPlus` because the comparison map
  is an isomorphism, `L` being exact: no resolutions are involved.
* `R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus` is the right derived functor of
  `R.mapHomotopyCategoryPlus ⋙ Qh ⋙ L.mapDerivedCategoryPlus` by the injective right
  derivability structure: the comparison map is `L.mapDerivedCategoryPlus` applied to the
  unit of `R.rightDerivedFunctorPlus`, which is an isomorphism on bounded below complexes
  of injectives.

Like `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`, this
file deliberately avoids the unbounded machinery indexed by K-injective complexes, whose
only source in this repository is a `sorry`; the bounded below statement rests on proved
theorems.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

instance isLeftDerivedFunctor_mapDerivedCategoryPlus :
    L.mapDerivedCategoryPlus.IsLeftDerivedFunctor L.mapDerivedCategoryPlusFactorsh.hom
      (HomotopyCategory.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryPlusFactorsh

instance isLeftDerivedFunctor_mapDerivedCategoryPlus_comp :
    (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)

instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp :
    (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnit L.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso D) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
      L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  have : IsIso (R.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι D).mapHomotopyCategoryPlus.obj X₁)) := inferInstance
  dsimp
  infer_instance

/-- The bounded below derived adjunction: for an adjunction `L ⊣ R` of additive functors
between abelian categories with `L` exact, the functor `L.mapDerivedCategoryPlus` induced
by `L` on the bounded below derived categories is left adjoint to the bounded below right
derived functor `R.rightDerivedFunctorPlus` of `R`. -/
noncomputable def derivedPlus :
    L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
  adj.mapHomotopyCategoryPlus.derived
    (HomotopyCategory.Plus.quasiIso C) (HomotopyCategory.Plus.quasiIso D)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnit

/-- The unit of the bounded below derived adjunction is determined by the unit of `adj`:
on the image of a bounded below complex `K`, it is the unit of `adj` on `K` followed by the
unit of the right derived functor of `R` at `L(K)`. -/
@[reassoc]
lemma derivedPlus_unit_app_fac (K : HomotopyCategory.Plus C) :
    adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) :=
  adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso C)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnit K

/-- The counit of the bounded below derived adjunction is determined by the counit of
`adj`, dually to `Adjunction.derivedPlus_unit_app_fac`. -/
@[reassoc]
lemma derivedPlus_counit_app_fac (M : HomotopyCategory.Plus D) :
    L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app M) ≫
        adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj M) =
      L.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj M) ≫
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app M) :=
  adj.mapHomotopyCategoryPlus.derivedε_fac_app (HomotopyCategory.Plus.quasiIso D)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnit M

/-- The formula of `Adjunction.derivedPlus_unit_app_fac` characterises the unit of the
bounded below derived adjunction: `L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus`
is a left derived functor, so a natural transformation into it is determined by its
components on the images of the bounded below homotopy category. -/
lemma derivedPlus_unit_eq
    (η : 𝟭 (DerivedCategory.Plus C) ⟶
      L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (h : ∀ K : HomotopyCategory.Plus C,
      η.app (DerivedCategory.Plus.Qh.obj K) ≫
          R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) =
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
          R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K)) :
    η = adj.derivedPlus.unit := by
  refine Functor.leftDerived_ext _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simpa using (h K).trans (adj.derivedPlus_unit_app_fac K).symm

end CategoryTheory.Adjunction
