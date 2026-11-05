/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # The quotient-completion unit on arbitrary complexes

Source: Stacks Tags 099M and 0941; naturality of localization and derived comparisons.
(blueprint: lem-constant-completion-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

attribute [local irreducible] ConstantCompletion.reductionTower
  ConstantCompletion.ordinaryUnit ConstantCompletion.reductionUnit
  ConstantCompletion.rlim ConstantCompletion.limitComparison ConstantCompletion.strictLimit

end CategoryTheory.ConstantCompletion
