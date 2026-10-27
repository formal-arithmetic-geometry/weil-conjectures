/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.AlgebraicGeometry.BlockStraighteningData

/-! # Auxiliary step of block straightening -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory
namespace AlgebraicGeometry.HilbertCoefficient

/-- The initial jets of the derivative equations: vanishing, triangularity, and
nonzero diagonal, before constructing any coefficient scheme.
Source: BM 1997 (9.7)--(9.8)(b), pp.279--280; step 1 of the stored block proof
(blueprint: lem-trf-block-straightening-initial-jet).

Proof: split beta into y and T exponents. The constant T coefficient of the mixed
partial is gamma! times the regular y derivative of c_gamma. Coordinate derivations
commute with the characterized Taylor map, so evaluation is beta! times its Taylor
coefficient. Its degree is one below the chosen vertex and hence the value is zero.
Differentiating once more gives the coefficient at beta+e_l with its factorial.
For j<l this is earlier in degree-lexicographic order than beta+e_j, so it is zero.
For l=j it is the nonzero initial coefficient times the vertex factorial. The
factorial is nonzero in the residue field, since it contains the characteristic-zero
base field. For r=0 all three indexed assertions are vacuous. -/
theorem blockStraighteningInitialJet {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r t s : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (a : B)
    (D : ImplicitCoordinateDerivations B c)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ)
    (A : BlockStraighteningInput B c a D α d Q f pick β) :
    (∀ j : Fin r, B.Γevaluation a (blockEquations D f pick β j) = 0) ∧
    (∀ j l : Fin r, j < l →
      B.Γevaluation a (D.deriv ⊤ (Sum.inr l) (blockEquations D f pick β j)) = 0) ∧
    (∀ j : Fin r,
      B.Γevaluation a (D.deriv ⊤ (Sum.inr j) (blockEquations D f pick β j)) ≠ 0) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
