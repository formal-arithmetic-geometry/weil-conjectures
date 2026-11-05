/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Functor naturality of the diagonal Roos comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local implicit_reducible] integralOperationsRoos scalarRoosMap
  Functor.mapHomologicalComplex

section FunctorNaturality
universe a b c d
variable {𝒜 : Type a} [Category.{b} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]
  {ℬ : Type c} [Category.{d} ℬ] [Abelian ℬ] [HasCountableProducts ℬ]

end FunctorNaturality

end WeilConjectures
