/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Data.Matrix.Mul
public import Sheaf.RingTheory.IsRegularSystemOfParameters

/-! # Formal Jacobian coordinate chain rule

Source: Stacks Project, Curves, Tag 0C4B (coordinate-change paragraph).
(blueprint: lem-trf-formal-jacobian-coordinate-chain-rule)
-/

@[expose] public section

universe u

namespace FormalJacobian

/-- The partial derivative in transported formal power-series coordinates.
Source: Stacks Project, Curves, Tag 0C4B (coordinate-change paragraph).
(blueprint: lem-trf-formal-jacobian-coordinate-chain-rule) -/
noncomputable def coordinatePartial {F : Type u} [Field F] {n : ℕ}
    (φ : MvPowerSeries (Fin n) F ≃ₐ[F] MvPowerSeries (Fin n) F)
    (k : Fin n) (h : MvPowerSeries (Fin n) F) : MvPowerSeries (Fin n) F :=
  φ (MvPowerSeries.pderiv F k (φ.symm h))

/-- The Jacobian matrix of a family of formal parameters in the original
coordinates. Source: Stacks Project, Curves, Tag 0C4B (coordinate-change
paragraph). (blueprint: lem-trf-formal-jacobian-coordinate-chain-rule) -/
noncomputable def jacobianQ {F : Type u} [Field F] {n : ℕ}
    (y : Fin n → MvPowerSeries (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) F) :=
  fun k i => MvPowerSeries.pderiv F i (y k)

/-- The Jacobian matrix of the original variables in transported coordinates.
Source: Stacks Project, Curves, Tag 0C4B (coordinate-change paragraph).
(blueprint: lem-trf-formal-jacobian-coordinate-chain-rule) -/
noncomputable def jacobianP {F : Type u} [Field F] {n : ℕ}
    (φ : MvPowerSeries (Fin n) F ≃ₐ[F] MvPowerSeries (Fin n) F) :
    Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) F) :=
  fun i k => coordinatePartial φ k (MvPowerSeries.X i)

/-- Formal partial derivatives obey the chain rule under a change of regular
parameters, and the two Jacobian matrices are inverse. The proof follows
Stacks Project, Curves, Tag 0C4B: truncate the transported series to finite
polynomials, apply the derivation Leibniz rule, and pass to the separated
power-series limit; identify the constant Jacobian on the cotangent quotient;
then apply both chain-rule identities to the coordinate elements. The empty
case is included because `Fin 0` indexes empty matrices and sums. Each step
uses the definitions of multivariate formal power series, regular systems of
parameters, and matrices recorded in the node dependencies.
(blueprint: lem-trf-formal-jacobian-coordinate-chain-rule) -/
theorem formal_jacobian_coordinate_chain_rule
    {F : Type u} [Field F] (n : ℕ)
    (y : Fin n → MvPowerSeries (Fin n) F)
    (φ : MvPowerSeries (Fin n) F ≃ₐ[F] MvPowerSeries (Fin n) F)
    (hφ : ∀ k : Fin n, φ (MvPowerSeries.X k) = y k)
    (hreg : IsLocalRing.IsRegularSystemOfParameters (List.ofFn y)) :
    (∀ (h : MvPowerSeries (Fin n) F) (i : Fin n),
      MvPowerSeries.pderiv F i h =
        ∑ k : Fin n, coordinatePartial φ k h * jacobianQ y k i) ∧
    (∀ (h : MvPowerSeries (Fin n) F) (k : Fin n),
      coordinatePartial φ k h =
        ∑ i : Fin n, MvPowerSeries.pderiv F i h * jacobianP φ i k) ∧
    (∃ Q₀ : Matrix (Fin n) (Fin n) F,
      (∀ k i, Q₀ k i = MvPowerSeries.constantCoeff (jacobianQ y k i)) ∧
      (∀ a b, ∑ j : Fin n, Q₀ a j *
          MvPowerSeries.constantCoeff (jacobianP φ j b) = if a = b then 1 else 0) ∧
      (∀ a b, ∑ j : Fin n, MvPowerSeries.constantCoeff (jacobianP φ a j) *
          Q₀ j b = if a = b then 1 else 0)) ∧
    (∀ a b, ∑ j : Fin n, jacobianQ y a j * jacobianP φ j b =
      if a = b then 1 else 0) ∧
    (∀ a b, ∑ j : Fin n, jacobianP φ a j * jacobianQ y j b =
      if a = b then 1 else 0) := by
  sorry

end FormalJacobian
