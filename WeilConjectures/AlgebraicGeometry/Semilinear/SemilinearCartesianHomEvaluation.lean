/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorCoherence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearCartesianProjection
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Cartesian internal Hom evaluation

Source: Zheng, Construction 4.1 and Proposition 4.17; Stacks Tags 06YY,
07A4, 07A6 and 08J9 (blueprint: lem-coef-semilinear-cartesian-hom-evaluation).
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
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

variable (S : SystemScalarCoherence.{c, v, r} J B τ)
  (T : SystemTensorCoherence.{c, v, r} J B τ S)

end WeilConjectures.SemilinearSections
