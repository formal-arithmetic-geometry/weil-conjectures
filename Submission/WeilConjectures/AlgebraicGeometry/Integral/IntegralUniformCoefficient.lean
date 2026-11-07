/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Submission.WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import Mathlib.AlgebraicGeometry.Noetherian
import Submission.WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite-extension specialization and scalars for the published complete category

Source: Weil blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The category is the published PbcIsBoundedConstructibleComplete, specialized to the
actual unlifted valuation ring in Type (u+1). Its completion, uniform reductions and
compatible origins are reused without redefining them. The published finite-extension
convenience abbreviation instead takes E in Type u and lifts its valuation ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The finite-extension valuation ring has the coefficient properties required by
this definition. Source: blueprint order 1300; Serre, Local Fields, Chapter II, §2
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the recorded valuation ring is a DVR with finite residue field. Its uniformizer
is nonzero and generates the maximal ideal. The ideal is principal and the ring is
Noetherian. The positive quotients are finite and have the length-one finite free
resolution given by multiplication by the corresponding uniformizer power; hence they
are perfect. The first quotient is a finite field of characteristic l, so it is torsion. -/
theorem pbcPadicCoefficientFacts (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
      (Ideal.span {Padic.coefficientExtensionUniformizer l E}).FG ∧
      (∀ x : Padic.coefficientExtensionIntegers l E ⧸
          Ideal.span {Padic.coefficientExtensionUniformizer l E},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (Padic.coefficientExtensionIntegers l E)
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) n) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  have hfinite (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨inferInstance, Submodule.fg_span_singleton _, ?_, hfinite, ?_⟩
  · have : Finite (Padic.coefficientExtensionIntegers l E ⧸
        Ideal.span {Padic.coefficientExtensionUniformizer l E}) := by
      simpa only [Padic.coefficientExtensionRing, Padic.coefficientExtensionIdeal,
        Nat.zero_add, pow_one]
        using hfinite 0
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n hn
    obtain ⟨P, hge, hle, hfree, _, hrest⟩ :=
      (AlgebraicGeometry.standard_quotients_perfect l n hn).2 E
    obtain ⟨_, _, _, φ, ε, hε, _, _, _⟩ := hrest
    have hqi : QuasiIso ε := by
      have hiso : IsIso (DerivedCategory.Q.map ε) := by
        rw [hε]
        infer_instance
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ε)).1 hiso
    let := HasDerivedCategory.standard
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    unfold adicQuotientPerfect
    refine ⟨P, -1, 0, hge, hle, ?_, ?_⟩
    · intro i
      have := (hfree i).1
      exact ⟨inferInstance, (hfree i).2⟩
    · exact ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩

/-- The actual p-adic coefficient datum, with its principal ideal and positive quotients.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcPadicCoefficientDatum (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E) where
  ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  noetherian := (pbcPadicCoefficientFacts l E).1
  finitelyGenerated := (pbcPadicCoefficientFacts l E).2.1
  quotientTorsion := (pbcPadicCoefficientFacts l E).2.2.1
  quotientFinite := (pbcPadicCoefficientFacts l E).2.2.2.1
  quotientPerfect := (pbcPadicCoefficientFacts l E).2.2.2.2

variable (T : Scheme.{u})

end AlgebraicGeometry.Scheme
