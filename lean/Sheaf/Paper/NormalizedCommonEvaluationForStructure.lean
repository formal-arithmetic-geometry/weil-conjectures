/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
import Sheaf.Paper.NormalizedRationalEvaluationNaturality

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

Proof: evaluation is inverse transposition of the identity. The normalization hS
therefore computes its representative by the rational inverse transpose of the
identity, conjugated by the specified Hom and tensor comparisons. For P, Q and g,
represent both components of g and the two evaluations over one finite field that
contains the original entry fields and the composita defining both Hom objects
and both tensor objects. Enlarge the field to represent all these finitely many
arrows simultaneously. The internal-Hom and tensor representative formulas
identify their maps with the finite rational maps, conjugated by the same
comparisons. At that field use normalizedRationalEvaluation_naturality. Cancel
adjacent comparisons and their inverses, then take the common-stage class. The
normalization hS holds at every further extension, so these representatives
compute the specified evaluations. No individual transition need be faithful.
Identity and zero arrows, repeated fields, and arbitrary localized sums are
included because rational evaluation naturality already holds for those. -/
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
      S.evaluation P ≫ g.hom.2 := by sorry

end WeilConjectures
