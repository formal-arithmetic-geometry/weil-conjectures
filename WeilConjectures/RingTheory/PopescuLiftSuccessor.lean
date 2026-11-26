/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.PopescuLiftQuotientData

/-!
# Induction step for lifting Popescu resolutions

Applying the lifting hypothesis for shorter lists, the quotient by the eighth power of the
first element can be resolved.

## Implementation details

`popescuEighthPowerLifting_tail` concludes only resolvability after quotienting by `π₀⁸`,
not the original problem.

## References

* [Stacks, Lemma 07F8] (case `r > 1`)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Resolve the quotient by the first eighth power by applying the shorter-list hypothesis. -/
theorem popescuEighthPowerLifting_tail
    (n : ℕ) (hn : 1 ≤ n) (ih : PopescuEighthPowerLifting.{u, v, w} n)
    (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (π : Fin (n + 1) → R) (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hπ : ∀ i : Fin (n + 1), algebraMap R Λ (π i) ∈ q.asIdeal)
    (hR : ∀ (i : Fin (n + 1))
      (x : R ⧸ Ideal.span {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hΛ : ∀ (i : Fin (n + 1))
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hstandard : ∀ i : Fin (n + 1), IsStrictlyStandardElement (R := R) (algebraMap R A (π i)))
    (hresolved : PopescuEighthPowerQuotientResolved (n + 1) π α q) :
    PopescuEighthPowerQuotientResolved 1 (fun _ ↦ π 0) α q := by
  obtain ⟨hfp, α₀, q₀, hα₀, hq₀, hπ₀, hR₀, hΛ₀, hstandard₀, hresolved₀⟩ :=
    popescuEighthPowerLifting_quotientData n hn R A Λ π α q hπ hR hΛ hstandard hresolved
  let J := Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8))
  let R₀ := R ⧸ J
  let A₀ := A ⧸ Ideal.map (algebraMap R A) J
  let Λ₀ := Λ ⧸ Ideal.map (algebraMap R Λ) J
  let τ : Fin n → R₀ := fun j ↦ Ideal.Quotient.mk J (π j.succ)
  have htail := ih R₀ A₀ Λ₀ τ α₀ q₀ hπ₀ hR₀ hΛ₀ hstandard₀ hresolved₀
  exact ⟨hfp, α₀, q₀, hα₀, hq₀, htail⟩

end Algebra
