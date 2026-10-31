/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization

/-! # Finite evaluation of the identity open on strict coefficient systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Tags 03DI and 03CY;
current blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-identity-open-system-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange

/-- The identity-open comparison determined by the system adjunction evaluates to
its finite counterpart through the specified open-evaluation mate.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03CY;
proper integral tower comparison, proof step 3
(blueprint: lem-weil-identity-open-system-evaluation).

Proof: on ordinary modules, identity open extension is the original presheaf
followed by sheafification. The comparison to the identity is the unique extension
of the identity on sections. The system adjunction and the finite adjunction have
these same section-normalized units. Evaluate the system identity-open comparison
at level n. The open-evaluation mate is defined by transposing the corresponding
pullback-evaluation square. Transpose both sides of the displayed equation using
the finite open adjunction. The unit equation for leftAdjointUniq changes the
left side to evaluation of the system unit; the mate equation changes the right
side to the same unit, with the identity pullback comparison. Both pullback
comparisons are the identity on sections. Equality of the transposes proves the
ordinary square. Exact open extension and exact finite evaluation descend this
square termwise to complexes and then to their localization. This proves the
formula for every unbounded system, including zero, without a constructibility
or boundedness hypothesis. -/
theorem identity_open_system_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) (M : coefficientSequenceDerived l E X) :
    letI := systemOpenEvaluationInv_isIso l E (𝟙 X) n
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((((systemDerivedOpenAdjunction l E (𝟙 X)).ofNatIsoRight
          (integralComparisonSystemUnit l E X)).leftAdjointUniq Adjunction.id).hom.app M) =
      (asIso (systemOpenEvaluationInv l E (𝟙 X) n)).inv.app M ≫
        (sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (n + 1)) X).hom.app
          ((coefficientSequenceDerivedEvaluation l E X n).obj M) := by sorry

end WeilConjectures.FrobeniusExchange
