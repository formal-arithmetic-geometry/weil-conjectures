/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionBasicData
import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionSupportEvaluationExistence
import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionScalarEvaluationXExistence
import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionScalarEvaluationYExistence
import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionRestrictionSupportExistence

/-! # Comparison data for normalized etale systems

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

/-- The sectionwise and mate comparisons associated to ordinary system operations.
Source: Zheng Lemma 5.16; Stacks 03D2, 03S2, 0GL6
(blueprint: lem-pur-etale-system-projection-existence).
-/
structure ComparisonData {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {l : ℕ} (b : BasicData c l) where
  supportEvaluation : ∀ (B : Coefficients.{u} l) (n : ℕ),
    SupportEvaluation (b.support B) n
      (b.evaluationX B n) (b.evaluationZ B n) (b.evaluationY B n)
  scalarEvaluationX : ∀ {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ),
    ScalarEvaluation X a (b.scalarX a) n
      (b.evaluationX B n) (b.evaluationX C n)
  scalarEvaluationY : ∀ {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ),
    ScalarEvaluation Y a (b.scalarY a) n
      (b.evaluationY B n) (b.evaluationY C n)
  restriction : ∀ {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings),
    RestrictionSupport a (b.support B) (b.support C)

/-- The ordinary comparisons exist with the section and mate normalizations.
Source: Zheng Lemma 5.16; Stacks 03D2, 03S2, 0GL6
(blueprint: lem-pur-etale-system-projection-comparison-data).

Proof: The proper comparison is the identity on sections and its inverse-image mate; the open
comparison is its exact localization mate. Scalar restriction is likewise fixed on
sections, and all derived comparisons are the canonical localizations. The mate-pasting
identities then provide the support, scalar-evaluation, and restriction fields. This
statement concerns comparison data for a fixed ordinary choice and is strictly weaker
than existence of a complete `Theory` record.
-/
theorem etaleSystemProjectionComparisonData_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) : Nonempty (ComparisonData b) := by
  classical
  refine ⟨{
    supportEvaluation := ?_
    scalarEvaluationX := ?_
    scalarEvaluationY := ?_
    restriction := ?_
  }⟩
  · intro B n
    exact (supportEvaluation_nonempty b B n).some
  · intro B C a n
    exact (scalarEvaluationX_nonempty b a n).some
  · intro B C a n
    exact (scalarEvaluationY_nonempty b a n).some
  · intro B C a
    exact (restrictionSupport_nonempty b a).some


end AlgebraicGeometry.Etale.SystemProjection
