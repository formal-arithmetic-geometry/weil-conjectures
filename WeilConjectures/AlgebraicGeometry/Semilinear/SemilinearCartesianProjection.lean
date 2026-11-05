/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearProjectionBelowFactorization
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos

/-! # Projection formula for cartesian semilinear systems

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YS, 07A4 and 08J9
(blueprint: lem-coef-semilinear-cartesian-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end WeilConjectures.SemilinearSections
