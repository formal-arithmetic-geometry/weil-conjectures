/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

/-!
# Heights are preserved by contraction along an integral extension with going down

## Main results

* `Ideal.height_under_eq_of_hasGoingDown`: if `S` is an integral `R`-algebra satisfying going
  down, then a prime `P` of `S` and its contraction `P ∩ R` have the same height.

Incomparability gives `height (P ∩ R) ≥ height P`: contracting along `algebraMap R S` is strictly
monotone on primes, so it carries a chain of primes below `P` to a chain of the same length
below `P ∩ R`. Going down gives the reverse inequality: a chain of primes below `P ∩ R` lifts to
a chain of primes below `P` of the same length.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is an integral `R`-algebra satisfying going down, then a prime `P` of `S` and its
contraction to `R` have the same height. -/
theorem Ideal.height_under_eq_of_hasGoingDown [Algebra.IsIntegral R S]
    [Algebra.HasGoingDown R S] (P : Ideal S) [P.IsPrime] :
    (P.under R).height = P.height := by
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) :=
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h
  have h1 : P.height = Order.height (⟨P, ‹_›⟩ : PrimeSpectrum S) :=
    PrimeSpectrum.height_eq_orderHeight (⟨P, ‹_›⟩ : PrimeSpectrum S)
  have h2 : (P.under R).height
      = Order.height (PrimeSpectrum.comap (algebraMap R S) (⟨P, ‹_›⟩ : PrimeSpectrum S)) :=
    PrimeSpectrum.height_eq_orderHeight
      (PrimeSpectrum.comap (algebraMap R S) (⟨P, ‹_›⟩ : PrimeSpectrum S))
  rw [h1, h2]
  refine le_antisymm (Order.height_le_iff'.mpr fun l hl ↦ ?_)
    (Order.height_le_height_apply_of_strictMono _ hmono _)
  have hlo : P.LiesOver l.last.asIdeal := by
    rw [hl]; exact Ideal.over_under P
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown (S := S) l P
  rw [← hlen, ← hlast]
  exact Order.length_le_height_last
