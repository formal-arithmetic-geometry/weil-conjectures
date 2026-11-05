/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Generic transition calculus for tensor presentations of strict systems

Source: Stacks 03CZ, 03EK, 07A4 and 0941.

Given two levels of a strict coefficient system, presentations of two system complexes
by scalar extensions of completed-coefficient complexes, and the ordinary evaluation and
scalar tensor comparisons, the induced presentation of the system tensor product is again
compatible with the strict transition maps. Everything here is stated for arbitrary ring
sheaves, so that kernel checking never compares the concrete coefficient rings.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures
namespace OrdinaryReductionTensor

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}

section Generators

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

end Generators

section ScalarNaturality

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

end ScalarNaturality

section TensorTransition

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r}]
  [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

end TensorTransition

end OrdinaryReductionTensor
end WeilConjectures
