/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The long exact sequence of a total right derived functor

Let `F : C ⥤ D` be an additive functor between abelian categories, `C` having K-injective
resolutions, and let `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` be a short exact sequence in `C`. Applying the
total right derived functor `RF` to the distinguished triangle `S₁ ⟶ S₂ ⟶ S₃ ⟶ S₁[1]` gives a
distinguished triangle in `D(D)`, whence a long exact sequence
`⋯ ⟶ Hⁿ(RF S₁) ⟶ Hⁿ(RF S₂) ⟶ Hⁿ(RF S₃) ⟶ Hⁿ⁺¹(RF S₁) ⟶ ⋯`
whose connecting maps are natural in morphisms of short exact sequences.

## Main results

- `CategoryTheory.Functor.rightDerivedHomologyδ`: the connecting morphism.
- `CategoryTheory.Functor.rightDerivedHomologySequence_exact₁`, `_exact₂`, `_exact₃`:
  exactness of the long exact sequence.
- `CategoryTheory.Functor.rightDerivedHomologyδ_naturality`: naturality of the connecting
  morphism.
-/

@[expose] public section

open CategoryTheory Limits Abelian Pretriangulated DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]

variable {S : ShortComplex C} (hS : S.ShortExact)

end CategoryTheory.Functor
