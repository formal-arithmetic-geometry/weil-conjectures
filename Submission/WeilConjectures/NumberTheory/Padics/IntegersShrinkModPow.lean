/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.NumberTheory.Padics.IntegersModPow
public import Submission.WeilConjectures.NumberTheory.Padics.Exponential
public import Submission.WeilConjectures.NumberTheory.Padics.IntegersNoetherian
public import Mathlib.Topology.LocallyConstant.Basic
public import Submission.WeilConjectures.RingTheory.CompleteLocalSubideal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The `ℓ`-adic reductions of `Shrink 𝒪_E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, with ring of integers `𝒪_E` and its universe
`u + 1` copy `Λ = Shrink 𝒪_E`, the coefficient ring of sheaves of `𝒪_E`-modules. This file
reconciles the two conventions for the torsion coefficients of the `ℓ`-adic formalism, the
discrete rings `𝒪_E ⧸ ℓⁿ = PadicAlgCl.integersModPow ℓ E n` and the quotients `Λ ⧸ (ℓ)ⁿ`:

- `PadicAlgCl.natCast_mem_nonZeroDivisors_shrink`, `PadicAlgCl.isAdicComplete_span_natCast_shrink`:
  `ℓ` is a nonzerodivisor of `Λ` and `Λ` is `ℓ`-adically complete (the hypotheses of the
  Bockstein finiteness theorems, with `ϖ = ℓ`);
- `PadicAlgCl.integersModPowEquivShrinkQuot`: `𝒪_E ⧸ ℓⁿ ≃ Λ ⧸ (ℓ)ⁿ`, compatibly with the
  reductions and the transition maps;
- `PadicAlgCl.isLocallyConstant_shrinkRingEquiv_smul`: `𝒪_E`, with its `ℓ`-adic topology, acts
  locally constantly on any `Λ`-module element killed by a power of `ℓ` (the hypothesis of
  `ModuleCat.towerLimit_isModuleTopology`).
-/

@[expose] public section

universe u

open Topology

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- `ℓ` is not a unit of `𝒪_E`: its norm is `ℓ⁻¹ < 1`. -/
lemma natCast_mem_maximalIdeal_integers (E : Type*) [Field E] [Algebra E (PadicAlgCl l)] :
    (l : integers l E) ∈ IsLocalRing.maximalIdeal (integers l E) := by
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu ↦ ?_)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h₁ : ‖algebraMap E (PadicAlgCl l) (v : E)‖₊ ≤ 1 := v.2
  have h₂ : algebraMap E (PadicAlgCl l) (l : E) * algebraMap E (PadicAlgCl l) (v : E) = 1 := by
    rw [← map_mul, ← map_one (algebraMap E (PadicAlgCl l))]
    congr 1
    exact_mod_cast congrArg (fun x : integers l E ↦ (x : E)) hv
  have h₃ : ‖algebraMap E (PadicAlgCl l) (l : E)‖₊ = 1 / (l : NNReal) := by
    rw [map_natCast]
    exact valuation_p l
  have h₄ := congrArg (‖·‖₊) h₂
  simp only [nnnorm_mul, nnnorm_one, h₃] at h₄
  have hl : (1 : NNReal) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have : 1 / (l : NNReal) * ‖algebraMap E (PadicAlgCl l) (v : E)‖₊ < 1 :=
    calc 1 / (l : NNReal) * ‖algebraMap E (PadicAlgCl l) (v : E)‖₊ ≤ 1 / (l : NNReal) * 1 :=
          by gcongr
      _ < 1 := by
          rw [mul_one, div_lt_one (by positivity)]
          exact hl
  exact this.ne h₄

variable (E : Type) [Field E] [Algebra E (PadicAlgCl l)]


/-- The image of `ℓ` in `Λ = Shrink 𝒪_E`. -/
lemma shrinkRingEquiv_natCast [Small.{u + 1} E] :
    shrinkRingEquiv l E (l : integers l E) = (l : Shrink.{u + 1} (integers l E)) :=
  map_natCast _ l


section Complete

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- `𝒪_E` is `ℓ`-adically complete: it is a complete noetherian local ring and `ℓ ∈ 𝔪_E`. -/
instance isAdicComplete_span_natCast_integers :
    IsAdicComplete (Ideal.span {(l : integers l E)}) (integers l E) :=
  IsAdicComplete.of_le_maximalIdeal _ _ ((Ideal.span_singleton_le_iff_mem _).2
    (natCast_mem_maximalIdeal_integers l E))

/-- `Λ = Shrink 𝒪_E` is `ℓ`-adically complete. -/
instance isAdicComplete_span_natCast_shrink [Small.{u + 1} E] :
    IsAdicComplete (Ideal.span {(l : Shrink.{u + 1} (integers l E))})
      (Shrink.{u + 1} (integers l E)) := by
  have h : (Ideal.span {(l : integers l E)}).map (shrinkRingEquiv.{0, u} l E) =
      Ideal.span {(l : Shrink.{u + 1} (integers l E))} := by
    rw [Ideal.map_span, Set.image_singleton, shrinkRingEquiv_natCast]
  rw [← h]
  exact (IsAdicComplete.congr_ringEquiv _ _).2 inferInstance

omit [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The ideal `(ℓ)` of `𝒪_E` is `𝔪_E`-primary: some power of every nonunit lies in it. -/
lemma maximalIdeal_le_radical_span_natCast :
    IsLocalRing.maximalIdeal (integers l E) ≤ (Ideal.span {(l : integers l E)}).radical := by
  intro x hx
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one (inv_prime_pos l) (norm_lt_one_of_mem_maximalIdeal l E hx)
  refine ⟨N, ?_⟩
  have h := (integersModPowMk_eq_zero_iff l E 1 (x ^ N)).2 (by
    rw [pow_one]
    simpa using hN.le)
  have h' := Ideal.Quotient.eq_zero_iff_mem.1 h
  rwa [pow_one] at h'

/-- `𝒪_E ⧸ ℓ` is finite: it is a quotient of some `𝒪_E ⧸ 𝔪_Eᴺ`. -/
instance finite_quotient_span_natCast_integers :
    Finite (integers l E ⧸ Ideal.span {(l : integers l E)}) := by
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (maximalIdeal_le_radical_span_natCast l E) (IsNoetherian.noetherian _)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hN)

/-- `Λ ⧸ ℓ` is finite for `Λ = Shrink 𝒪_E`. -/
instance finite_quotient_span_natCast_shrink [Small.{u + 1} E] :
    Finite (Shrink.{u + 1} (integers l E) ⧸ Ideal.span {(l : Shrink.{u + 1} (integers l E))}) :=
  have h : (Ideal.span {(l : integers l E)}).map (shrinkRingEquiv.{0, u} l E) =
      Ideal.span {(l : Shrink.{u + 1} (integers l E))} := by
    rw [Ideal.map_span, Set.image_singleton, shrinkRingEquiv_natCast]
  Finite.of_equiv _ (Ideal.quotientEquiv _ _ (shrinkRingEquiv.{0, u} l E) h.symm).toEquiv

/-- `𝒪_E ⧸ ℓⁿ` is finite. -/
instance finite_quotient_span_natCast_pow_integers (n : ℕ) :
    Finite (integers l E ⧸ Ideal.span {(l : integers l E)} ^ n) := by
  have hr : IsLocalRing.maximalIdeal (integers l E) ≤
      (Ideal.span {(l : integers l E)} ^ n).radical := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [pow_zero, Ideal.one_eq_top, Ideal.radical_top]
      exact le_top
    · rw [Ideal.radical_pow _ hn]
      exact maximalIdeal_le_radical_span_natCast l E
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr (IsNoetherian.noetherian _)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hN)

/-- `Λ ⧸ ℓⁿ` is finite for `Λ = Shrink 𝒪_E`. -/
instance finite_quotient_span_natCast_pow_shrink [Small.{u + 1} E] (n : ℕ) :
    Finite (Shrink.{u + 1} (integers l E) ⧸
      Ideal.span {(l : Shrink.{u + 1} (integers l E))} ^ n) :=
  have h : (Ideal.span {(l : integers l E)} ^ n).map (shrinkRingEquiv.{0, u} l E) =
      Ideal.span {(l : Shrink.{u + 1} (integers l E))} ^ n := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, shrinkRingEquiv_natCast]
  Finite.of_equiv _ (Ideal.quotientEquiv _ _ (shrinkRingEquiv.{0, u} l E) h.symm).toEquiv

end Complete

variable [Small.{u + 1} E]

lemma map_span_natCast_pow_shrinkRingEquiv (n : ℕ) :
    (Ideal.span {(l : integers l E) ^ n}).map (shrinkRingEquiv.{0, u} l E) =
      Ideal.span {(l : Shrink.{u + 1} (integers l E))} ^ n := by
  rw [Ideal.map_span, Set.image_singleton, map_pow, shrinkRingEquiv_natCast,
    Ideal.span_singleton_pow]

/-- **The two conventions for the torsion coefficients agree**: `𝒪_E ⧸ ℓⁿ ≃ Λ ⧸ (ℓ)ⁿ` for
`Λ = Shrink 𝒪_E`. -/
noncomputable def integersModPowEquivShrinkQuot (n : ℕ) :
    integersModPow l E n ≃+*
      Shrink.{u + 1} (integers l E) ⧸ Ideal.span {(l : Shrink.{u + 1} (integers l E))} ^ n :=
  Ideal.quotientEquiv _ _ (shrinkRingEquiv.{0, u} l E)
    (map_span_natCast_pow_shrinkRingEquiv l E n).symm

@[simp]
lemma integersModPowEquivShrinkQuot_mk (n : ℕ) (x : integers l E) :
    integersModPowEquivShrinkQuot.{u} l E n (integersModPowMk l E n x) =
      Ideal.Quotient.mk _ (shrinkRingEquiv.{0, u} l E x) :=
  rfl


end PadicAlgCl
