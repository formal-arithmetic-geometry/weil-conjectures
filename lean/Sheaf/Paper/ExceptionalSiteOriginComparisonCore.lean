/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Core data for bounded-below site comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

/-- The fixed evaluation functor preserves a common lower bound.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison-bound).

The proof is the levelwise exactness argument: evaluation is exact and therefore
commutes with the standard truncation and lower-bound predicates. -/
theorem exceptionalSiteOriginComparison_evaluation_bound
    (O : Type (u + 1)) [CommRing O] (ell : O)
    (T : Scheme.{u})
    (P : CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell)) :
    ∀ n M (a : ℤ), M.IsGE a → ((P.evaluation n).obj M).IsGE a := by
  sorry


/-- The finite inverse image preserves lower bounds.
Source: Zheng Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison-level-bound). -/
theorem exceptionalSiteOriginComparison_level_inverse_bound
    (O : Type (u + 1)) [CommRing O] (ell : O)
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell)
    (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) (N : DerivedCategory (strictEtaleLevel T O ell n)) (a : ℤ)
    (hN : N.IsGE a) : ((C.image.level n).inverse.obj N).IsGE a := by
  sorry

/-- The site comparison core, before the final evaluation-origin projection.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1.
(blueprint: lem-sf-exceptional-site-origin-comparison-core).

Construct the ordinary and derived comparison at the prescribed evaluation package,
then apply the finite comparison at each quotient level. The system unit and counit
are detected by the evaluations, and the scalar mate squares give normalization. This
statement records the construction and comparison properties; evaluation-origin
projection is handled separately by the preceding exactness lemma. -/
theorem exceptionalSiteOriginComparison_core
    (O : Type (u + 1)) [CommRing O] (ell : O)
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (T : Scheme.{u}) (PE : StrictEtaleEvaluation T O ell) :
    ∃ C : ExceptionalSystemSiteComparison O ell T PE,
      ExceptionalSystemSiteEquivalence C ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        IsIso ((C.image.level n).adjunction.unit.app M)) ∧
      (∀ n M, C.levelOrigin n M →
        IsIso ((C.image.level n).adjunction.counit.app M)) ∧
      (∀ n M, (∃ a : ℤ, M.IsGE a) →
        C.levelOrigin n ((C.image.level n).inverse.obj M)) := by
  sorry

end AlgebraicGeometry
