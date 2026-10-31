/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites

/-! # Preservation by completed system pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Completed pullback computed as the actual total limit of the strict pullback
system preserves integral constructibility and the input finite Tor interval.
Source: prop-coef-integral-exceptional-adjoint, paragraph 1; steps 2--4 of
lem-coef-integral-dual-exceptional-system
(blueprint: lem-coef-completed-system-pullback-preservation).

Proof: The reduction system of P is normalized. Exact coefficient-system inverse
image commutes with quotient scalar extension, by
lem-pur-coefficient-system-derived-comparison. Thus the transition adjunct of its
pullback is the pullback of an invertible transition adjunct. This proves the
normalization asserted here as a property of the actual strict pullback system.
The coefficient-ring hypotheses hold because the extension integers form a DVR
and are complete: compatible residues admit Cauchy lifts with a unique limit in
the closed unit ball. Identify the total-limit model with integralDerivedPullback
using its normalized descent on K-flat representatives, whose finite projections
are the same counit adjuncts. IntegralOperations_preserve_constructible now gives
constructibility. The reconstruction counit for the normalized pullback is an
isomorphism. Evaluate it and compose reductionEvaluation and the canonical
pullback-evaluation comparison: its source is the reduction of the total limit,
and its target is finite pullback of the reduction of P. Apply
sf_pullback_torAmplitude at every level and transport its unchanged interval
through this isomorphism. No duality or exceptional operation is used. The
argument includes empty schemes, zero complexes, and a=b. -/
theorem completedSystemPullbackPreservation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus l E Y)
    (P : sfIntegralConstructibleCategory l E Y) :
    let N := (integralComparisonDerivedSequencePullback l E f).obj (S.reduction.obj P.obj)
    let F := (coefficientSequenceLimit l E X).obj N
    sfIntegralConstructible l E X F ∧ IsNormalizedCoefficientSequence l E X N ∧
      (∀ (a b : ℤ), a ≤ b →
        (∀ n : ℕ, HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E Y n).obj P.obj) a b) →
        ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X n).obj F) a b) := by sorry

end WeilConjectures
