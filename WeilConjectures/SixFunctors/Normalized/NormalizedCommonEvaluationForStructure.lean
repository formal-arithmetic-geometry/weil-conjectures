/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
import WeilConjectures.PoincareDuality.NormalizedCommonEvaluationNaturality

/-! # Naturality of common-stage Hom-first evaluation

Source: Bhatt--Scholze, Lemma 3.4.11 and Proposition 6.8.14;
the pair-naturality part of the common-stage transpose argument, step 6
(blueprint: lem-sf-normalized-common-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
  [∀ x : X, Invertible (l : X.residueField x)]

attribute [local irreducible] commonStageDerivedTensor commonStageDerivedInternalHom
  commonStageTensorComparison commonStageHomComparison

/-- The normalized common-stage counit is natural in both entries of a permitted pair.
Source: Bhatt--Scholze, Lemma 3.4.11 and Proposition 6.8.14; the pair-naturality
argument of lem-sf-adic-common-stage-hom-transpose, step 6
(blueprint: lem-sf-normalized-common-evaluation-naturality).

Proof: the uniqueness clause of podCommonClosed_existsUnique identifies S with
podCommonClosed, since both satisfy the same finite-stage normalization. Replace
S by this equal closed structure and apply normalizedCommonEvaluation_naturality.
This equality identifies the whole transpose, so its inverse at the identity,
and hence evaluation, also agrees. The canonical naturality theorem covers
arbitrary permitted pairs and pair morphisms without extra hypotheses. -/
theorem normalizedCommonEvaluationForStructure_naturality
    (S : PodPartialClosed (commonStageDerivedTensor l Ω X)
      (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X))
    (hS : PodCommonTransposeNormalization l Ω X S)
    (P Q : (commonStageHomPairs l Ω X).FullSubcategory) (g : P ⟶ Q) :
    (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom ((commonStageDerivedInternalHom l Ω X).map g) (𝟙 Q.obj.1.unop)) ≫
      S.evaluation Q =
    (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom l Ω X).obj P)) g.hom.1.unop) ≫
      S.evaluation P ≫ g.hom.2 := by
  have hU := (podCommonClosed_existsUnique l Ω X).unique hS
    (podCommonClosed_existsUnique l Ω X).exists.choose_spec
  rw [hU]
  exact normalizedCommonEvaluation_naturality l Ω X P Q g

end WeilConjectures
