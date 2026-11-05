/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Horizontal coherence of additive Roos comparisons
(blueprint: lem-pur-additive-roos-horizontal). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section RoosCoherence
attribute [local implicit_reducible] integralOperationsRoos
  Functor.mapHomologicalComplex CochainComplex.mappingCocone

open CochainComplex CochainComplex.HomComplex
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
  {D : Type v} [Category.{w} D] [Abelian D] [HasCountableProducts D]

end RoosCoherence

end WeilConjectures
