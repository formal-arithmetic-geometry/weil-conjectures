/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorCompatibility
public import Sheaf.Paper.PointFibreDerivedTensorScalar
/-! # Finite point tensor comparisons and coefficient quotients

Source: Stacks 07A4 and 06YY.
(blueprint: lem-sf-point-finite-tensor-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- Canonical finite point comparisons, simultaneously compatible with every quotient.
Source: Stacks 07A4, 06YY
(blueprint: lem-sf-point-finite-tensor-comparisons).

Proof: evaluate module sheaves at the identity geometric point. The normalized
ringed-point model identifies its section ring with the coefficient ring by the
constant-section map. Transport the model through this ring isomorphism. Its signed
pure-tensor map descends through the K-flat localization, including arbitrary K-flat
representatives by comparison with flat-term resolutions. Finite-Tor constructible
objects and the coefficient unit form a tensor subcategory, so restrict the source
constraints and the strong comparison. For each quotient, descend the balanced
scalar map on K-flat resolutions. On generators both tensor-square composites send
a tensor x tensor y to the two factors with coefficient one. Naturality and
localization give the square on all objects, also for an identity quotient. -/
theorem pointFiniteTensorComparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    ∃ F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorData D l E n,
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (n : ℕ),
        PointFiniteSourceConstraints D l E n (F E n) ∧
          PointFiniteTensorCanonical D l E n (F E n)) ∧
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (m n : ℕ) (h : n ≤ m),
        PointFiniteTensorReductionData D l E h (F E m) (F E n) := by
  sorry

end WeilConjectures
