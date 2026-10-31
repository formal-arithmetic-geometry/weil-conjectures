/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionScalarEvaluationYExistence
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionRestrictionSupportExistence

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

end AlgebraicGeometry.Etale.SystemProjection
