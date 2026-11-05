/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES

/-!
# The truncation couple

Source: Weil conjectures blueprint, sec-abelian-varieties, cor-pqf-proper-quasifinite-finite,
node def-sp-truncation-couple, order 520 (blueprint: def-sp-truncation-couple).

The terms use the chosen-resolution convention of `def-sp-kinjective-bridge`.
The maps are transported from the image of the canonical truncation triangle
under the K-injective right derived functor. Exactness is a separate statement,
`lem-sp-truncation-couple-exact`; it is not a field of the construction here.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory
namespace TruncationCouple

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

section Derived

variable [HasDerivedCategory A]

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
  [IsGrothendieckAbelian.{v₁} A] [IsGrothendieckAbelian.{v₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

end Derived
end TruncationCouple

end CategoryTheory
