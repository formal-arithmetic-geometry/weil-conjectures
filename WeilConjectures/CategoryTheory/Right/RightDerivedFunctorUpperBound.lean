/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Upper bounds for right derived functors of finite cohomological dimension

Source: Stacks Project, Tag 07K7, lemma-unbounded-right-derived, part (4)(c).
-/

@[expose] public section

set_option autoImplicit false

universe w v u v' u'

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D] [HasInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

variable [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C] [IsGrothendieckAbelian.{w} C]

end CategoryTheory.Functor
