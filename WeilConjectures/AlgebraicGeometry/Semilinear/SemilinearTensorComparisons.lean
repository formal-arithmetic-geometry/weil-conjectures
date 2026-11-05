/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorBase
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearScalarTensor

/-! # Evaluation and scalar tensor comparisons for semilinear systems
Source: Zheng Construction 4.1 and Stacks 06YY, 07A4.
(blueprint: lem-coef-semilinear-tensor-coherence-comparisons)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
variable (S : SystemScalarCoherence.{c, v, r} J B τ)
end WeilConjectures.SemilinearSections
