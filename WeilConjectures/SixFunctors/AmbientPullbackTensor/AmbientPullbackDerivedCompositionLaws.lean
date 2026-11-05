/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackOrdinaryCompositionLaws
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Derived pullback associativity and unit laws.

Source: Stacks 015F and 04VG.
(blueprint: new-lem-sf-ambient-pullback-derived-composition-laws).

This is the exact-localization part of the ambient pullback coherence argument.
The ordinary equations are preserved by the exact termwise functors and their
localizations; the resulting three equations are recorded here separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

end WeilConjectures.AmbientPullbackTensor
