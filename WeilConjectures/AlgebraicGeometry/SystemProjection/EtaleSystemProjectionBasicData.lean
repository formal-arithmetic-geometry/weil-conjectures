/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData

/-! # Ordinary operations for normalized etale systems

Source: Zheng, Constructions 4.1 and 5.14--5.15; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The ordinary support, evaluation, and scalar operations needed before comparison data.
Source: Zheng Constructions 4.1 and 5.14--5.15; Stacks 03D2, 03S2, 07A4
(blueprint: lem-pur-etale-system-projection-existence).

The construction uses the actual sequence-site module operations, their exact evaluation
functors, and the fixed derived scalar models. The sectionwise comparison fields are
provided separately by `EtaleSystemProjectionComparisonData`.
-/
structure BasicData {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (l : ℕ) where
  support : ∀ B : Coefficients.{u} l, Support c B.rings
  evaluationX : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation X B.rings n
  evaluationZ : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation c.Z B.rings n
  evaluationY : ∀ (B : Coefficients.{u} l) (n : ℕ), Evaluation Y B.rings n
  scalarX : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings), Scalar X a
  scalarY : ∀ {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings), Scalar Y a

end AlgebraicGeometry.Etale.SystemProjection
