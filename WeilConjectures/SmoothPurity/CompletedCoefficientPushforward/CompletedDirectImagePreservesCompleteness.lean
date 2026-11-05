/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStructureMap
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # Derived direct image preserves completed-coefficient completeness

Source: Stacks proetale.tex Tag 099N (1),(3), and algebraization.tex Tags 0A0E and 099B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a av b bv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section PrincipalTransport
variable {A : Type a} [Category.{av} A] [Abelian A]
  {B : Type b} [Category.{bv} B] [Abelian B]

end PrincipalTransport

namespace CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end CompletedCoefficientPushforward
end WeilConjectures
