/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Bounds and conservativity of exact derived adjunctions

Source: Stacks Project, Derived Categories, Tags 015F and 05TC; Zheng,
Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a av b bv da db
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (fac : DerivedCategory.Q ⋙ FD ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

include F fac

end CategoryTheory
