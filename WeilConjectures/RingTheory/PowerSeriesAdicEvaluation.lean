/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Algebra.MvPolynomial.Eval
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete

/-!
# Evaluation of power series in an adically complete ring

Evaluation of multivariate power series at finitely many elements of an ideal of an adically
complete ring is the unique continuous ring map with the prescribed constants and variables.

## Implementation details

`F.truncTotal N` retains exactly the coefficients of total degree less than `N`, so
`MvPolynomial.eval₂ α b (F.truncTotal N)` is the finite sum of the `α(c_ν) * b^ν` with
`|ν| < N`; the value of the evaluation is characterized by these reductions.

## References

* [Stacks, Tag 07NL] and [Stacks, Tag 07NN] (proofs, universal property of power series rings)
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- Evaluation at finitely many elements of an ideal of an adically complete ring is the
unique continuous ring map with the prescribed constants and variables. Its value is uniquely
characterized by its reductions. -/
theorem exists_unique_adic_evaluation {C : Type u} {T : Type v}
    [CommRing C] [CommRing T] (α : C →+* T) (I : Ideal T) [IsAdicComplete I T]
    (n : ℕ) (b : Fin n → T) (hb : ∀ i : Fin n, b i ∈ I) :
    ∃ E : MvPowerSeries (Fin n) C →+* T,
      (∀ c : C, E (MvPowerSeries.C c) = α c) ∧
      (∀ i : Fin n, E (X i) = b i) ∧
      (∀ N : ℕ, ∃ M : ℕ,
        ∀ F ∈ (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) C))) ^ M,
          E F ∈ I ^ N) ∧
      (∀ E' : MvPowerSeries (Fin n) C →+* T,
        (∀ c : C, E' (MvPowerSeries.C c) = α c) →
        (∀ i : Fin n, E' (X i) = b i) →
        (∀ N : ℕ, ∃ M : ℕ,
          ∀ F ∈ (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) C))) ^ M,
            E' F ∈ I ^ N) →
        E' = E) ∧
      (∀ (F : MvPowerSeries (Fin n) C) (t : T),
        (∀ N : ℕ, 1 ≤ N →
          Ideal.Quotient.mk (I ^ N) t =
            Ideal.Quotient.mk (I ^ N) (MvPolynomial.eval₂ α b (F.truncTotal N))) ↔
        t = E F) := by
  obtain ⟨E, hC, hX, hred, huniq⟩ :=
    exists_ringHom_of_isAdicComplete I α n b hb
  refine ⟨E, hC, hX, ?_, ?_, hred⟩
  · intro N
    refine ⟨N, ?_⟩
    have hvars : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) C)) ≤
        I.comap E := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change E (X i) ∈ I
      rw [hX]
      exact hb i
    intro F hF
    exact ((pow_le_pow_left' hvars N).trans (Ideal.le_comap_pow E N)) hF
  · intro E' hC' hX' _
    exact huniq E' hC' hX'

end MvPowerSeries
