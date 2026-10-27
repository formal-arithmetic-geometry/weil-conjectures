/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleSystemProjectionBasicData

/-! # Support evaluation comparison existence for normalized etale systems

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The normalized support evaluation comparison exists at each coefficient level.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-support-evaluation-existence).

Proof: Use the identity-on-sections proper direct-image comparison and its inverse-image
mate, then apply the exact open localization mate and paste the two factors. The derived
comparison is the canonical localization of this ordinary mate, with the prescribed
section normalization.
-/
theorem supportEvaluation_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) (B : Coefficients.{u} l) (n : ℕ) :
    Nonempty (SupportEvaluation (b.support B) n
      (b.evaluationX B n) (b.evaluationZ B n) (b.evaluationY B n)) := by sorry

end AlgebraicGeometry.Etale.SystemProjection
