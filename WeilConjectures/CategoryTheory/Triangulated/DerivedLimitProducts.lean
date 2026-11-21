/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties

@[expose] public section
universe t w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Exact countable products descend to the derived category and commute with homology.
Source: Stacks Project, Derived Categories, Lemma 13.34.2, Tag 07KC. -/
theorem derivedCategory_countableProducts_core
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] :
    ∃ hP : HasCountableProducts (DerivedCategory A),
      letI : HasCountableProducts (DerivedCategory A) := hP
      (∀ (J : Type t) [Countable J] (C : J → CochainComplex A ℤ),
        Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C))))) ∧
      (∀ (J : Type t) [Countable J] (p : ℤ),
        PreservesLimitsOfShape (Discrete J) (DerivedCategory.homologyFunctor A p)) := by
  let hP : HasCountableProducts (DerivedCategory A) :=
    derivedCategory_hasCountableProducts A
  have hprops := @derivedCategory_countableProducts_properties A _ _ _ _ _ hP
  exact ⟨hP, hprops⟩

end CategoryTheory
