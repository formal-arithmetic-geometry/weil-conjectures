/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionBasicData

/-! # Target scalar evaluation comparison existence for normalized etale systems

Source: Zheng, Construction 4.1, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The normalized scalar evaluation comparison exists on the target scheme.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-scalar-evaluation-y-existence).

Proof: The ordinary restriction-of-scalars comparison is identity on sections. Its
canonical derived localization and the normalized scalar adjunction mate give the
specified scalar evaluation comparison.
-/
theorem scalarEvaluationY_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :
    Nonempty (ScalarEvaluation Y a (b.scalarY a) n
      (b.evaluationY B n) (b.evaluationY C n)) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
