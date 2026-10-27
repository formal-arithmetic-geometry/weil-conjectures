/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.CompletedPullbackTowerTensorLevel

/-! The adjacent transition square for the normalized coherent tensor tower.

Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-level-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Consecutive components of the normalized tensor tower comparison commute with the
actual quotient transitions `n + 1 → n`.
Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-level-transition).
Proof: write `τ_n : B_{n+1} → B_n` for the quotient map, `t_n` for the horizontal
transitions and `a_n` for the reduction evaluation `B_n ⊗_A M ≅ e_n r M` of the core,
whose transpose is `ν_n = π_n ∘ η⁰_M`.
(1) The limit cone gives `t_n ν_{n+1} = ν_n`, so on local pure tensors
`t_n a_{n+1}(b ⊗ x) = τ_n(b) ν_n(x) = a_n(τ_n(b) ⊗ x)`; pure tensors generate the presheaf
tensor and sheafification extends the equality, so `a_n` and `a_n⁻¹` intertwine the quotient
transitions, termwise on `P` and `Q` (`pullbackTensorReductionEvaluationComplex`).
(2) With `C = r P`, `D = r Q`, the evaluation tensor isomorphism
`κ_n : e_n Tot(C, D) ≅ Tot_{B_n}(e_n C, e_n D)` (`coefficientEvaluationTensorIso`) is the
ordinary evaluation comparison on every `(p,q)` summand.
(3) The cochain tensor reduction identity of the semilinear sections calculus, transposed
through scalar extension/restriction, says that under `κ_{n+1}`, `κ_n` the total-system
transition is `x ⊗ y ↦ t_n x ⊗ t_n y`; restricting scalars along `A → B_{n+1} → B_n`
keeps this an equality of `A`-linear cochain maps.
(4) The first factor `pullbackTensorRestrictedLevel` commutes with the transitions by the
definition of the restricted tower; the target transition of the strict finite tensor tower
sends `(b ⊗ x) ⊗ (c ⊗ y)` to `(τ_n b ⊗ x) ⊗ (τ_n c ⊗ y)`. Tensoring the two squares of (1),
pasting with (3) and (4) and using functoriality of the total tensor gives the square. -/
theorem pullbackTensorTensorTowerLevel_transition
    (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorTensorTowerLevel l E W P Q (n + 1)).hom ≫
        ((integralOperationsTensorTowerFunctor l E W).obj (P,Q)).map
          (homOfLE (Nat.le_succ n)).op =
      (pullbackTensorRestrictedTower l E W
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)))
        ).map (homOfLE (Nat.le_succ n)).op ≫
      (pullbackTensorTensorTowerLevel l E W P Q n).hom := by
  sorry

end WeilConjectures
