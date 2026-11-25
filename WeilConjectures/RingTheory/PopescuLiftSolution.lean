/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.PopescuLiftOne
import WeilConjectures.RingTheory.PopescuLiftSuccessor

/-!
# Lifting a Popescu resolution modulo eighth powers

In Situation 07F7, a resolution of the problem modulo the eighth powers of a list of strictly
standard elements lifts to a resolution of the original local problem.

## Implementation details

The reduced algebra structures are Mathlib's `Ideal.Quotient.algebraQuotientMapQuotient`
instances; the reduced map and prime are specified by their compatibility with the quotient
maps, which determines them uniquely. The finite-presentation witness (true by base change)
is included only to type the recorded definition of `CanBePopescuResolved`. The annihilator
equalities are expressed pointwise as equivalences of vanishing products.

## References

* [Stacks, Lemma 07F8], in [Stacks, Situation 07F7]
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem quotient_ann_transport {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {I K : Ideal S} (he : I = K) (a : R)
    (h : ∀ x : S ⧸ K, a • x = 0 ↔ a ^ 2 • x = 0) :
    ∀ x : S ⧸ I, a • x = 0 ↔ a ^ 2 • x = 0 := by
  let e := (Ideal.quotientEquivAlgOfEq R he).toLinearEquiv
  intro x
  have hax := h (e x)
  have heq (b : R) : b • e x = 0 ↔ b • x = 0 := by
    rw [← e.map_smul, ← e.map_zero]
    exact e.injective.eq_iff
  exact (heq a).symm.trans (hax.trans (heq (a ^ 2)))

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
variable (r : ℕ) (π : Fin r → R)

local notation "J" => Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
local notation "J_A" => Ideal.map (algebraMap R A) J
local notation "J_Λ" => Ideal.map (algebraMap R Λ) J
local notation "R₀" => R ⧸ J
local notation "A₀" => A ⧸ J_A
local notation "Λ₀" => Λ ⧸ J_Λ

/-- A resolution modulo all the eighth powers lifts to the original local problem. -/
theorem canBePopescuResolved_of_quotient_eighth_powers
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) (hr : 1 ≤ r)
    (hπ : ∀ i : Fin r, algebraMap R Λ (π i) ∈ q.asIdeal)
    (hR : ∀ (i : Fin r)
      (x : R ⧸ Ideal.span {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hΛ : ∀ (i : Fin r)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin r, j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hstandard : ∀ i : Fin r, IsStrictlyStandardElement (R := R) (algebraMap R A (π i)))
    (hresolved :
      ∃ (_ : FinitePresentation R₀ A₀) (α₀ : A₀ →ₐ[R₀] Λ₀) (q₀ : PrimeSpectrum Λ₀),
        α₀.toRingHom.comp (Ideal.Quotient.mk J_A) =
          (Ideal.Quotient.mk J_Λ).comp α.toRingHom ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
        CanBePopescuResolved α₀ q₀) :
    CanBePopescuResolved α q := by
  have lift : ∀ n, 1 ≤ n → PopescuEighthPowerLifting.{u, v, w} n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact popescuEighthPowerLifting_one
    | succ n hn ih =>
      intro R A Λ _ _ _ _ _ _ _ π α q hπ hR hΛ hstandard hresolved
      have hfirst := popescuEighthPowerLifting_tail n hn ih R A Λ π α q
        hπ hR hΛ hstandard hresolved
      apply popescuEighthPowerLifting_one R A Λ (fun _ ↦ π 0) α q
      · exact fun _ ↦ hπ 0
      · intro i
        apply quotient_ann_transport (R := R) _ (π 0) (hR 0)
        congr 1
        ext y
        simp
      · intro i
        apply quotient_ann_transport (R := R) _ (π 0) (hΛ 0)
        congr 1
        ext y
        simp
      · exact fun _ ↦ hstandard 0
      · exact hfirst
  exact lift r hr R A Λ π α q hπ hR hΛ hstandard hresolved

end Algebra
