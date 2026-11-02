/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCohomologySheaves

/-! # The recorded Tate twists in the PBC finite-stage coordinates

Source: blueprint def-coefficient-twists-detailed, signed powers and tensor with a complex;
Bhatt--Scholze, Section 6.8 (blueprint: def-coefficient-twists-detailed).
All roots, signed powers and coefficient identifications are the published ones.
The only new construction is their transport to the PBC completed coefficient ring.
The original finite, integral, rational and intrinsic Qbar interfaces remain imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]

end AlgebraicGeometry.Scheme
