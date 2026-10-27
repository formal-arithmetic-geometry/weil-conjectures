/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.FiniteCompactScalarConstructible

/-! # Evaluation of the proper/open scalar word

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941, 06YY and 07A6;
the compact-support paragraph of `lem-fix-operation-reduction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- Finite evaluation of compact support on an arbitrary derived system. Both
factors are the specified direct-image and open-adjunction evaluation mates.
Source: Zheng 4.10 (blueprint: lem-sf-compact-scalar-evaluation-square). -/
def systemCompactEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) := by
  letI := systemDirectEvaluation_isIso l E c.g n
  letI := systemOpenEvaluationInv_isIso l E c.i n
  exact Functor.isoWhiskerLeft (systemDerivedOpen l E c.i)
      (asIso (systemDirectEvaluation l E c.g n)) ≪≫
    Functor.isoWhiskerRight (asIso (systemOpenEvaluationInv l E c.i n)).symm
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing l E (n + 1)))

/-- The evaluated system scalar word is the intrinsic finite scalar transpose,
through scalar evaluation and the fixed proper/open evaluation maps. This is an
identity of arrows for arbitrary systems, without constructibility, boundedness,
Noetherian, completeness or cartesian-system hypotheses.

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941, 06YY, 07A6;
`lem-fix-operation-reduction`, compact-support paragraph, and step 3 of
`lem-sf-compact-support-system-scalar-finite-invertible`.
(blueprint: lem-sf-compact-scalar-evaluation-square).

Proof: on the vertical sequence site use the compatible quotient ring maps
induced by the embedding. The ScalarSystems evaluation comparison is the
transpose of identity-on-sections restriction evaluation. Transport its source
model to integralComparisonSequenceScalarModel using the unique isomorphism of
universal cochain left-derived pairs. Transport each target model to the fixed
pbcDerivedExtend in the same way. This gives the scalar evaluation isomorphisms
s below, normalized on K-flat representatives by tensor evaluation.

Evaluate the unit, pullback/scalar comparison, and counit defining
systemDirectScalar. The unit and counit equations in AdjunctionEvaluation and
SemilinearSections.evaluation_mate identify the resulting word with the finite
proper scalar mate. For the open factor apply that calculation to the exact
open adjunction; evaluation preserves its inverse because the open mate is an
isomorphism. The resulting finite open map is the transpose of sfOpenRestriction.
Scalar mate pasting identifies the composite of these two transposes with the
transpose of sfCompactSupportRestriction, namely intrinsicCompactScalar.
Naturality moves the two scalar evaluation comparisons to the ends and gives
exactly the displayed equality, using the specified systemCompactEvaluation.
All equations are checked on the same ordinary units and universal cochain
counits before localization; no equality is inferred from derived evaluations.
The construction includes n=0, zero complexes, empty schemes and identity
embeddings, and does not require any finite quotient map to be flat. -/
theorem systemCompactScalar_evaluation_square
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    ∃ s : ∀ W : Scheme.{u},
      integralComparisonDerivedSequenceScalar l E L ι W ⋙
          coefficientSequenceDerivedEvaluation l L W n ≅
        coefficientSequenceDerivedEvaluation l E W n ⋙
          pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) W),
      ∀ N : coefficientSequenceDerived l E X,
        (coefficientSequenceDerivedEvaluation l L Y n).map
            ((systemCompactScalar l E L ι c).app N) ≫
          (systemCompactEvaluation l L c n).hom.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l L (n + 1))).map
            ((s X).hom.app N) =
        (s Y).hom.app ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj N) ≫
          (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y)).map
            ((systemCompactEvaluation l E c n).hom.app N) ≫
          (intrinsicCompactScalar (integralScalarQuotientMap l E L ι n) c).app
            ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by sorry

end WeilConjectures.FrobeniusExchange
