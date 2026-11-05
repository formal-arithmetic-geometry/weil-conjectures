/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Comparison squares and direct-sum totalization -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local implicit_reducible] CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.map₂HomologicalComplex
open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

local notation "Tot[" F "]" => CategoryTheory.Functor.uncurry.obj
  (CategoryTheory.Functor.map₂HomologicalComplex F
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasCoproducts.{0} D]
  (C : A ⥤ B) (U : B ⥤ D) (I : A ⥤ D)
  [C.Additive] [U.Additive] [I.Additive] [U.IsEquivalence]
  (FA : A ⥤ A ⥤ A) (FB : B ⥤ B ⥤ B) (FD : D ⥤ D ⥤ D)
  [FA.PreservesZeroMorphisms] [∀ M, (FA.obj M).PreservesZeroMorphisms]
  [FB.PreservesZeroMorphisms] [∀ M, (FB.obj M).PreservesZeroMorphisms]
  [FD.PreservesZeroMorphisms] [∀ M, (FD.obj M).PreservesZeroMorphisms]

end HomologicalComplex
