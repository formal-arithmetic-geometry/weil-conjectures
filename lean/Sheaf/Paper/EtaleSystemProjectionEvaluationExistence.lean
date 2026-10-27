/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionData

/-! # Evaluation operations for normalized etale systems

Source: Zheng, Construction 4.1; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-evaluation-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The exact evaluation functors exist at every coefficient level on all three schemes.
Source: Zheng Construction 4.1; Stacks 03D2, 03S2, 07A4
(blueprint: lem-pur-etale-system-projection-evaluation-existence).

Proof: Evaluate strict module systems at a fixed vertical level, where exactness is
computed componentwise. Compose with restriction from the constant ring sheaf to the
constant module sheaf; finite limits and colimits are preserved by the sectionwise
constant-sheaf construction and its sheafification. Package the resulting additive,
finite-limit-preserving, and finite-colimit-preserving instances for X, Z, and Y.
-/
theorem etaleSystemProjectionEvaluationData_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    Nonempty
      ((∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation X B.rings n) ∧
        (∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation c.Z B.rings n) ∧
          (∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation Y B.rings n)) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
