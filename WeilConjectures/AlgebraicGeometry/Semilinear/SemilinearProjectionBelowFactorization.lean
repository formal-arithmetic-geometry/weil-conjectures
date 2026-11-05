/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCore
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSingletonEvaluationMate
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence

/-! # Below-level factorization of the singleton projection

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YS, 07A4 and 08J9
(blueprint: lem-coef-semilinear-projection-below-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
section CategoricalFactorization
universe a a' b b' d d'
variable {X : Type a} [Category.{a'} X] {Y : Type b} [Category.{b'} Y]
  {Z : Type d} [Category.{d'} Z]

end CategoricalFactorization

namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end WeilConjectures.SemilinearSections
