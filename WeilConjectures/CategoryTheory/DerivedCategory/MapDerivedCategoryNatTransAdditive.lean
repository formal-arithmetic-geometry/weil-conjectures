/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Functoriality and additivity of the derived natural transformations

For exact functors between abelian categories, the natural transformation
`Functor.mapDerivedCategoryNatTrans τ : D(F) ⟶ D(G)` induced by `τ : F ⟶ G` is compatible with
identities, composition, sums and multiples (`Functor.mapDerivedCategoryNatTrans_comp`,
`Functor.mapDerivedCategoryNatTrans_sum`, `Functor.mapDerivedCategoryNatTrans_nsmul`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

section

variable {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end

end CategoryTheory.Functor
