/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentationPaste

/-! # Forgetting an exactly derived descent square -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

open DerivedPresentation

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B C' D' C D : Type*}
  [Category A] [Category B] [Category C'] [Category D'] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C'] [Abelian D'] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C'] [HasDerivedCategory D'] [HasDerivedCategory C] [HasDerivedCategory D]
  (L : A ⥤ B) (T : A ⥤ C') (S : B ⥤ D') (U : C' ⥤ C) (V : D' ⥤ D)
  (R : C ⥤ D) (RW : C' ⥤ D')
  [L.Additive] [T.Additive] [S.Additive] [U.Additive] [V.Additive]
  [R.Additive] [RW.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits RW] [PreservesFiniteColimits RW]

end CategoryTheory.Functor
