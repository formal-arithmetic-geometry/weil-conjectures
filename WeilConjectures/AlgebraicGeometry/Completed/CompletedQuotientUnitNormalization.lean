/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedReductionUnit
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Normalization of the actual completed quotient unit

Source: Stacks Tags 03CR, 05RR, 06YY and 0941.
(blueprint: lem-weil-pbc-completed-quotient-unit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

section CompletionNormalization
variable {B H : Type*} [Category* B] [Category* H] [Abelian B] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory H] [Abelian.HasKInjectiveResolutions H]
  (G : B ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (R : H ⥤ B) [R.Additive] (adj : G ⊣ R)

end CompletionNormalization

attribute [local irreducible] completedReductionTower completedReductionTowerCounit
  completedReductionModuleUnit completedReductionTowerUnit

end AlgebraicGeometry.Scheme
