/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization

/-! # Evaluation of the specified proper/open system exchange

Source: Zheng, Construction 4.1 and Lemma 4.10; Deligne, Weil II (1.1.14).
This is the forward compatibility step of the whole-system inverse argument.
(blueprint: lem-weil-system-compact-exchange-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

/-- Evaluation carries the actual proper/open system composite to the specified
finite compact exchange, through the canonical evaluation comparisons.
Source: Zheng, Construction 4.1 and Lemma 4.10; Deligne, Weil II (1.1.14), p. 153;
agent-written compatibility argument extracted from steps 1--2 of
lem-weil-frobenius-system-exchange-inverse.
(blueprint: lem-weil-system-compact-exchange-evaluation).
Proof: expand systemCompactExchange into the proper mate and proper image of the
open exchange. Apply systemExchange_evaluation to the proper factor. The open
factor is the inverse left mate of the pullback square. Evaluate its unit,
counit and pullback compositor using the section-normalized evaluation mates;
the mate-pasting identity identifies the result with the inverse finite open
mate. The canonical field of SfOpenSquareExchangeData identifies this with the
specified finite open exchange. Naturality of direct-image evaluation moves the
open factor past the proper comparison. Compose the two equations and cancel
the middle pullback-coordinate isomorphisms. The two remaining comparisons are
exactly S and T below, and the finite composite is finiteCompact. This calculation
uses actual mate words, never faithfulness of evaluation. It applies to arbitrary
unbounded systems, including zero systems and the identity or empty open. -/
theorem systemCompactExchange_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)
    (n : ℕ) (C : coefficientSequenceDerived l E X) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let d := isoWhiskerLeft (systemDerivedOpen l E c.i)
        (@asIso _ _ _ _ (systemDirectEvaluation l E c.g n)
          (systemDirectEvaluation_isIso l E c.g n)) ≪≫
      isoWhiskerRight
        (@asIso _ _ _ _ (systemOpenEvaluationInv l E c.i n)
          (systemOpenEvaluationInv_isIso l E c.i n)).symm
        (proEtaleConstantDerivedDirectImage c.g A)
    let EX := coefficientSequenceDerivedEvaluation l E X n
    let EY := coefficientSequenceDerivedEvaluation l E Y n
    let S := (systemPullEvaluation l E gY n).symm.app
        ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj C) ≪≫
      (sfIntrinsicDerivedPullback A gY).mapIso (d.app C) ≪≫
      (openSquareDerivedPullbackModel A gY).symm.app
        ((sfIntrinsicCompactSupport c A).obj (EX.obj C))
    let T := d.app ((integralComparisonDerivedSequencePullback l E gX).obj C) ≪≫
      (sfIntrinsicCompactSupport c A).mapIso
        ((systemPullEvaluation l E gX n).symm.app C ≪≫
          (openSquareDerivedPullbackModel A gX).symm.app (EX.obj C))
    EY.map ((systemCompactExchange l E c gX gB gY wp sj).app C) ≫ T.hom =
      S.hom ≫ (finiteCompact l E (n + 1) (Nat.succ_pos n) c gX gB gY wp sj).app
        (EX.obj C) := by sorry

end WeilConjectures.FrobeniusExchange
