/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs

/-!
# Compatibility of the unbounded right derived functor with `rightDerivedFunctorPlus`

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has
enough injectives and K-injective resolutions. This file identifies the restriction
of the unbounded total right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` to the bounded below
derived category with the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`:

`F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
  DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor`

(`Functor.rightDerivedFunctorPlusCompatibility`).

The proof is by uniqueness of right derived functors: both sides are right derived
functors of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι`
with respect to the quasi-isomorphisms of the bounded below homotopy category. By the
injective right derivability structure `HomotopyCategory.Plus.localizerMorphism`, it
suffices to check that the corresponding units are isomorphisms on bounded below
complexes of injectives:

- for `F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι`, whose unit is obtained by
  whiskering `F.rightDerivedFunctorPlusUnit` with the inclusion, this holds since the
  unit of `F.rightDerivedFunctorPlus` is an isomorphism on complexes of injectives;
- for `DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor`, whose unit is obtained by
  whiskering `F.rightDerivedFunctorUnit` with the inclusion of the bounded below
  homotopy category, this holds since a bounded below complex of injectives is
  K-injective and the unit of `F.rightDerivedFunctor` is an isomorphism on K-injective
  complexes.
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [HasKInjectiveResolutions C]

/-- The unit exhibiting `F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι` as a right
derived functor of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
DerivedCategory.Plus.ι`, obtained by whiskering `F.rightDerivedFunctorPlusUnit` with the
inclusion of the bounded below derived category. -/
noncomputable def rightDerivedFunctorPlusιUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι

instance : (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    (fun X₁ ↦ inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁)))))

/-- The unit exhibiting `DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor` as a right
derived functor of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
DerivedCategory.Plus.ι`, obtained by whiskering `F.rightDerivedFunctorUnit` with the
inclusion of the bounded below homotopy category. -/
noncomputable def ιRightDerivedFunctorUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι C) F.rightDerivedFunctorUnit

instance : (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor).IsRightDerivedFunctor
    F.ιRightDerivedFunctorUnit (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    (fun X₁ ↦ by
      obtain ⟨X₁, hX₁⟩ := X₁
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X₁
      obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hX₁
      have hinj : ∀ (i : ℤ), Injective
          ((((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i) :=
        fun i ↦ inferInstanceAs (Injective ((InjectiveObject.ι C).obj (K.X i)))
      have : CochainComplex.IsKInjective
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
        CochainComplex.isKInjective_of_injective _ n
      exact inferInstanceAs (IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))))

/-- The restriction of the unbounded total right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` to the bounded below
derived category identifies with the right derived functor
`F.rightDerivedFunctorPlus` on the bounded below derived categories. -/
noncomputable def rightDerivedFunctorPlusCompatibility :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor :=
  Functor.rightDerivedUnique _ _ F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
    (HomotopyCategory.Plus.quasiIso C)

end Functor

end CategoryTheory
