/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.FiniteFieldFiber

/-! # Quotient transitions under the specified system direct-image evaluations

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tag 0D6E;
current blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-system-evaluation-transitions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange

/-- Exact completed-coefficient restriction of the specified direct-image evaluations
carries the strict quotient maps to the published compact and ordinary transitions.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 0D6E;
proper integral tower comparison, proof steps 2 and 3
(blueprint: lem-weil-proper-system-evaluation-transitions).

Proof: choose a single flat-term K-flat representative of K. Its reduction system
has the actual quotient chain maps, by the reductionModel clause of the recorded
coefficient calculus. For the star system apply the derived section direct image
on the sequence site. The evaluation mate is computed by one simultaneous
K-injective replacement, so the evaluated quotient map is the finite direct image
of the quotient map, followed by the ordinary restriction-of-scalars comparison.
This is exactly sfDirectImageTransition, including its restriction associator.
For the compact system insert exact identity-open extension before the same system
direct image. The open-evaluation mate identifies the quotient map with the finite
open-extension quotient map. The open restriction square and the same proper
restriction square paste to sfCompactSupportTransition. Restrict both calculations
through the completed coefficient projection. The sectionwise associativity of
restriction identifies the pasted restrictions with the published completed
restriction associator. Exact descent of these chain-map equations gives the two
assertions for arbitrary unbounded K. No invertibility of a reduction comparison
is used. The construction is unchanged for K zero, empty schemes or f identity. -/
theorem proper_system_evaluation_transitions
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    letI := systemDirectEvaluation_isIso l E f n
    letI := systemDirectEvaluation_isIso l E f (n + 1)
    let M₁ := ((reduction l E X) ⋙
      (systemDerivedOpen l E (𝟙 X) ⋙ systemDirect l E f)).obj K
    let M₂ := ((reduction l E X) ⋙ systemDirect l E f).obj K
    let a := fun i : ℕ ↦
      (coefficientRestrictedEvaluationIso l E Y i).app M₁ ≪≫
        (scalarReductionDerivedRestriction l E Y i).mapIso
          ((compactFiniteEvaluation l E (Compactification.ofIsProper f) i).app K)
    let b₀ :=
      (coefficientRestrictedEvaluationIso l E Y n).app M₂ ≪≫
        (scalarReductionDerivedRestriction l E Y n).mapIso
          ((asIso (systemDirectEvaluation l E f n)).app ((reduction l E X).obj K) ≪≫
            (proEtaleConstantDerivedDirectImage f
              (Padic.coefficientExtensionRing l E (n + 1))).mapIso
                ((((models l E).system X).reductionEvaluation n).app K))
    let b₁ :=
      (coefficientRestrictedEvaluationIso l E Y (n + 1)).app M₂ ≪≫
        (scalarReductionDerivedRestriction l E Y (n + 1)).mapIso
          ((asIso (systemDirectEvaluation l E f (n + 1))).app ((reduction l E X).obj K) ≪≫
            (proEtaleConstantDerivedDirectImage f
              (Padic.coefficientExtensionRing l E ((n + 1) + 1))).mapIso
                ((((models l E).system X).reductionEvaluation (n + 1)).app K))
    ((normalizedDVRTowerTransition l E Y D hl n.le_succ).app
        ((coefficientSequenceDerivedRestriction l E Y).obj M₁) ≫ (a n).hom =
      (a (n + 1)).hom ≫ sfCompactSupportTransition l E
        (Compactification.ofIsProper f) K n) ∧
    ((normalizedDVRTowerTransition l E Y D hl n.le_succ).app
        ((coefficientSequenceDerivedRestriction l E Y).obj M₂) ≫ b₀.hom =
      b₁.hom ≫ sfDirectImageTransition l E f K n) := by sorry

end WeilConjectures.FrobeniusExchange
