/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteLevels
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacks
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Constructibility of all reductions from the first

The integral category `D(X_proet, O_E)` is `AdicCompletion.Modules l E X`, internal
modules over the pulled-back condensed integer ring `DerivedNakayama.integerRing l E`;
`AdicCompletion.derivedReduction l E X n` is the derived reduction `K_{n+1}` modulo
`pi_E^(n+1)`. Bounded constructibility over `O_E` and over `O_E/pi_E^n` is the single
finite-constant-model predicate `constantModelBoundedConstructible`, applied to the
respective condensed rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a derived-complete integral pro-étale complex `K` on a Noetherian scheme, the
first reduction `K_1` is bounded constructible if and only if every reduction `K_n`
is bounded constructible with cohomology in one interval `[r,s]` independent of `n`
(first conjunct); and `K` itself lies in `D_bc(X, O_E)` if and only if this second
condition holds (second conjunct). -/
theorem integralCriterionReductions (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : IsDerivedComplete l E X K) :
    (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ↔
      (∀ n : ℕ, constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧
        ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K))) ∧
    (constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
      (∀ n : ℕ, constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧
        ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K))) := by
  have hfirst : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) →
      (∀ n : ℕ, constantModelBoundedConstructible
        (DerivedNakayama.quotientRing l E (n + 1)) X
        ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
      ∃ r s : ℤ, r ≤ s ∧
        ∀ (n : ℕ) (q : ℤ), q < r ∨ s < q →
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((AdicCompletion.derivedReduction l E X n).obj K)) := by
    intro h₁
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h₁.1
    have hbound (q : ℤ) (hq : q < a ∨ max a b < q) : IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          ((AdicCompletion.derivedReduction l E X 0).obj K)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ a).1 ha q hq
      · exact (DerivedCategory.isLE_iff _ b).1 hb q (lt_of_le_of_lt (le_max_right a b) hq)
    obtain ⟨hn, -, -⟩ := integral_finite_levels l E X K hK h₁ a (max a b) (le_max_left a b)
      hbound
    refine ⟨fun n ↦ (hn n).1, a, max a b, le_max_left a b, fun n q hq ↦ ?_⟩
    obtain ⟨hge, hle⟩ := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn (hn n).2
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).1 hge q hq
    · exact (DerivedCategory.isLE_iff _ (max a b)).1 hle q hq
  exact ⟨⟨hfirst, fun h ↦ h.1 0⟩,
    fun h ↦ hfirst (IntegralModelsStacks.internal_integral_criterion_forward l E X K h).2.1,
    fun h ↦ IntegralModelsStacks.internal_integral_criterion_reverse l E X K hK (h.1 0)⟩

end AlgebraicGeometry.ProEtale
