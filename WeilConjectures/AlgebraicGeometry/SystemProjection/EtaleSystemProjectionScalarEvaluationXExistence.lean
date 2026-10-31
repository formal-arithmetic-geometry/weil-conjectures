/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionScalarEvaluationYExistence
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionSupportExistence
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionEvaluationExistence
/-! # Source scalar evaluation comparison existence for normalized etale systems

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

/-- The normalized scalar evaluation comparison exists on the source scheme.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-scalar-evaluation-x-existence).

Proof: specialize target scalar evaluation existence to the identity compactification
of X. Construct its ordinary support and evaluation data, replacing both evaluation
families by the prescribed source evaluations and both scalar families by the
prescribed source scalar models. The target comparison is then exactly the required
source comparison, including all its normalization fields.
-/
theorem scalarEvaluationX_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :
    Nonempty (ScalarEvaluation X a (b.scalarX a) n
      (b.evaluationX B n) (b.evaluationX C n)) := by
  classical
  let c' : Compactification (𝟙 X) := Compactification.ofIsProper (𝟙 X)
  obtain ⟨support'⟩ := etaleSystemProjectionSupportData_nonempty c' l
  obtain ⟨⟨_, evaluationZ', _⟩⟩ := etaleSystemProjectionEvaluationData_nonempty c' l
  let b' : BasicData c' l :=
    { support := support'
      evaluationX := b.evaluationX
      evaluationZ := evaluationZ'
      evaluationY := b.evaluationX
      scalarX := b.scalarX
      scalarY := b.scalarX }
  simpa [b', c'] using
    (scalarEvaluationY_nonempty (b := b') (a := a) (n := n))

end AlgebraicGeometry.Etale.SystemProjection
