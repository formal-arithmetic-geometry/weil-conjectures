/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Left exact upper truncation comparisons

Source: Stacks Project, Tag 05TC (2), and the canonical cycle calculation of Tag 0AVW.
(blueprint: lem-sc-left-exact-upper-truncation-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

variable [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

end CategoryTheory.Functor
