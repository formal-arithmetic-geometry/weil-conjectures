/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoefficientLimit
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Ordinary tensor models of finite-free coefficient cones

Source: Stacks Project, Tag 09C6, the finite-free coefficient calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section TensorPowers
variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteProducts C]
  {r : ℕ} {M : C} (e₀ : M ≅ ∏ᶜ (fun _ : Fin r ↦ 𝟙_ C))

end TensorPowers

end AlgebraicGeometry.Scheme
