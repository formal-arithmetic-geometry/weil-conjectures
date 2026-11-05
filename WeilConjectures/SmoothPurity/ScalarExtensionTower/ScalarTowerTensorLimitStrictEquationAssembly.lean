/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitRepresentativeTransport
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Representative and limit transport

The scalar/tensor comparison is transported in two separate stages.  The first
stage is the strict calculation on K-flat good representatives.  The second
stage is the localization, completion, and total-limit argument.  Keeping the
representative equality as an explicit hypothesis makes the latter a genuine
transport statement rather than a restatement of DerivedSigmaModel.
(blueprint: stage3-pur-scalar-tensor-limit-strict-equation-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor scalarReduction tensorReduction
  integralComparisonDerivedSequenceScalar

end WeilConjectures.ScalarExtensionTower
