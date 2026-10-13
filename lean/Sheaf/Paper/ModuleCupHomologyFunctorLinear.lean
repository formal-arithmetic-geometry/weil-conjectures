/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Linearity of derived module homology

Source: Stacks Project, Tag 064B, Lemma 13.19.8.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable (k : Type u) [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- The derived module homology functor is k-linear, by descent from complex homology.
Source: Mathlib's Localization.functor_linear_iff and ShortComplex.homologyFunctor_linear.
(blueprint: lem-sc-module-cup-homology-functor-linear) -/
theorem cupHomologyFunctor_linear (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).Linear k := by
  have : (HomologicalComplex.shortComplexFunctor
      (ModuleCat.{u} k) (ComplexShape.up ℤ) n).Linear k := by
    constructor
    intro A B f r
    rfl
  have : (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} k) (ComplexShape.up ℤ) n).Linear k := by
    change ((HomologicalComplex.shortComplexFunctor
      (ModuleCat.{u} k) (ComplexShape.up ℤ) n) ⋙
      ShortComplex.homologyFunctor (ModuleCat.{u} k)).Linear k
    infer_instance
  let : Localization.Lifting (DerivedCategory.Q : _ ⥤ DerivedCategory (ModuleCat.{u} k))
      (HomologicalComplex.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) n)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n⟩
  exact (Localization.functor_linear_iff
    (DerivedCategory.Q : _ ⥤ DerivedCategory (ModuleCat.{u} k))
    (HomologicalComplex.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ)) k
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) n)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n)).mp inferInstance

end
end AlgebraicGeometry.Scheme.Modules
