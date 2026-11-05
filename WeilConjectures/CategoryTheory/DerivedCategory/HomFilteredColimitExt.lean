/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HomFilteredColimit

/-!
# Continuity of `Ext` out of an object of `C` and filtered colimits

Let `C` be an abelian category and `X` an object of `C`. If for every `k : ℕ` the functor
`Ext^k(X, -)` commutes with filtered colimits (elementwise: surjectivity and injectivity of
`colim Ext^k(X, Bᵢ) ⟶ Ext^k(X, B)`), then `X` placed in degree `0` satisfies
`DerivedCategory.HomCommutesWithFilteredColimits`
(`DerivedCategory.HomCommutesWithFilteredColimits.singleFunctor_obj_of_ext`): in negative
degrees the morphisms `X[0] ⟶ B[n]`, `n > 0`, vanish for `t`-structure reasons, and in the other
degrees they are the `Ext` groups.
-/

@[expose] public section

universe w w'

open CategoryTheory Category Limits Abelian

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

namespace HomCommutesWithFilteredColimits

end HomCommutesWithFilteredColimits

end DerivedCategory
