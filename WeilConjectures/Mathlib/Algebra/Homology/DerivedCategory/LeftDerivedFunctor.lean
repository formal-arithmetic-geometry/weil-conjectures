/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureKProjectives

/-!
# The left derived functor on the unbounded derived category

If `F : C ⥤ D` is an additive functor between abelian categories, where `C`
has K-projective resolutions, we define the left derived functor
`F.leftDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` between the
corresponding unbounded derived categories.

This is the dual of
`WeilConjectures/SixFunctors/Preliminaries/RightDerivedFunctor.lean`.
It relies on the K-projective derivability structure
`HomotopyCategory.KProjectives.localizerMorphism` at the level of homotopy
categories, where the source category is equipped with the class of
isomorphisms. As a consequence, any functor from
`HomotopyCategory C (ComplexShape.up ℤ)` has a (pointwise) left derived
functor with respect to quasi-isomorphisms, and the counit of such a derived
functor is an isomorphism on K-projective complexes.

In mathlib, this file would be
`Mathlib/Algebra/Homology/DerivedCategory/LeftDerivedFunctor.lean`.

-/

@[expose] public section

open CategoryTheory Abelian Limits

variable {C H : Type*} [Category C] [Abelian C] [Category H]

namespace HomotopyCategory

namespace KProjectives

variable [HasKProjectiveResolutions C]

section

variable (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)

omit [HasKProjectiveResolutions C] in
lemma localizerMorphism_derives : (localizerMorphism C).Derives F :=
  MorphismProperty.isInvertedBy_isomorphisms _

/-- Any functor from the unbounded homotopy category of an abelian category
with K-projective resolutions has a left derived functor with respect to
quasi-isomorphisms. -/
instance : F.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (localizerMorphism_derives F).hasPointwiseLeftDerivedFunctor

variable [HasDerivedCategory C] (F' : DerivedCategory C ⥤ H)
  (α : DerivedCategory.Qh ⋙ F' ⟶ F)
  [F'.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

instance (K : CochainComplex C ℤ) [K.IsKProjective] :
    IsIso (α.app ((quotient _ _).obj K)) :=
  (localizerMorphism_derives F).isIso_of_isLeftDerivedFunctor α (mk K)

end

end KProjectives

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [HasKProjectiveResolutions C]

/-- The left derived functor `DerivedCategory C ⥤ DerivedCategory D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has K-projective resolutions. -/
noncomputable def leftDerivedFunctor :
    DerivedCategory C ⥤ DerivedCategory D :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The natural transformation that is part of the data of
the left derived functor `DerivedCategory C ⥤ DerivedCategory D`
when `F : C ⥤ D` is an additive functor between abelian categories and
`C` has K-projective resolutions. -/
noncomputable def leftDerivedFunctorCounit :
    DerivedCategory.Qh ⋙ F.leftDerivedFunctor ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalLeftDerivedCounit
    DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

instance :
    F.leftDerivedFunctor.IsLeftDerivedFunctor
      F.leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [leftDerivedFunctor, leftDerivedFunctorCounit]
  infer_instance

example (K : CochainComplex C ℤ) [K.IsKProjective] :
    IsIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj K)) := by
  infer_instance

end Functor

end CategoryTheory
