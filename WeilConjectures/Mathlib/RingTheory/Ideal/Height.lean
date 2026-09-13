/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Heights of contracted primes and of primes in a quotient

## Main results

* `Ideal.height_le_height_under`: for an integral extension `R ⊆ S`, a prime `P` of `S` has
  height at most the height of its contraction `P ∩ R`.
* `Algebra.HasGoingDown.height_under_le_height`: if `S` satisfies going down over `R`, the
  contraction `P ∩ R` of a prime `P` has height at most the height of `P`.
* `Algebra.HasGoingDown.height_under`: for an integral extension satisfying going down, a prime
  and its contraction have the same height. This is the analogue for such extensions of
  `IsLocalization.height_under`.
* `Ideal.height_map_quotientMk_of_covBy`: if `q` covers `p` in the prime spectrum of `R`, then
  the image of `q` in `R ⧸ p` has height one.
* `Ideal.height_add_ringKrullDim_quotient_le`: `height p + dim (R ⧸ p) ≤ dim R` for a prime `p`
  of any commutative ring `R`.

`Algebra.HasGoingDown.height_under` overlaps with Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, which writes the height of `P` as the
height of `P ∩ R` plus the height of `P` in the fibre over `P ∩ R`: an integral extension has
zero-dimensional fibres, so the two statements agree. It is proved directly here because the
general statement assumes `S` Noetherian, which is not available in the intended application.
-/

@[expose] public section

section GoingDown

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- For an integral extension `R ⊆ S`, a prime `P` of `S` has height at most the height of its
contraction to `R`. -/
theorem Ideal.height_le_height_under [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.under R).height := by
  -- contracting along `algebraMap R S` is strictly monotone on primes, by incomparability
  have h := Order.height_le_height_apply_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h) (⟨P, ‹_›⟩ : PrimeSpectrum S)
  rwa [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h

-- `Ideal.exists_ltSeries_of_hasGoingDown` needs this option in Mathlib too.
set_option backward.isDefEq.respectTransparency.types false in
/-- If `S` satisfies going down over `R`, then the contraction to `R` of a prime `P` of `S` has
height at most the height of `P`. -/
theorem Algebra.HasGoingDown.height_under_le_height [Algebra.HasGoingDown R S] (P : Ideal S)
    [P.IsPrime] : (P.under R).height ≤ P.height := by
  have h : Order.height (PrimeSpectrum.comap (algebraMap R S) (⟨P, ‹_›⟩ : PrimeSpectrum S))
      ≤ Order.height (⟨P, ‹_›⟩ : PrimeSpectrum S) := by
    -- a chain of primes below `P ∩ R` lifts to a chain of primes below `P` of the same length
    refine Order.height_le_iff'.mpr fun l hl ↦ ?_
    have : P.LiesOver l.last.asIdeal := by
      rw [hl]
      exact Ideal.over_under P
    obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown (S := S) l P
    rw [← hlen, ← hlast]
    exact Order.length_le_height_last
  rwa [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h

/-- If `S` is an integral `R`-algebra satisfying going down, then a prime `P` of `S` and its
contraction to `R` have the same height. -/
theorem Algebra.HasGoingDown.height_under [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : (P.under R).height = P.height :=
  le_antisymm (Algebra.HasGoingDown.height_under_le_height R P) (Ideal.height_le_height_under R P)

end GoingDown

variable {R : Type*} [CommRing R]

/-- If `q` covers `p` in the prime spectrum of `R`, then the image of `q` in `R ⧸ p` has
height one. -/
theorem Ideal.height_map_quotientMk_of_covBy {p q : PrimeSpectrum R} (h : p ⋖ q) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height = 1 := by
  have hle : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.asIdeal_le_asIdeal p q).mpr h.lt.le
  have hmk (Q : Ideal (R ⧸ p.asIdeal)) : p.asIdeal ≤ Q.comap (Ideal.Quotient.mk p.asIdeal) := by
    simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using
      Ideal.comap_mono (f := Ideal.Quotient.mk p.asIdeal) (bot_le : ⊥ ≤ Q)
  have hprime : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).comap (Ideal.Quotient.mk p.asIdeal)
      = q.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
  refine le_antisymm ?_ (Order.one_le_iff_ne_zero.mpr ?_)
  · rw [← Nat.cast_one (R := ℕ∞), Ideal.height_le_iff]
    intro Q hQ hQlt
    have hQc : (Q.comap (Ideal.Quotient.mk p.asIdeal)).IsPrime := inferInstance
    -- a prime strictly below `q ⧸ p` contracts to a prime strictly between `p` and `q`
    have hlt : Q.comap (Ideal.Quotient.mk p.asIdeal) < q.asIdeal := by
      rw [← hcomap]
      refine lt_of_le_of_ne (Ideal.comap_mono hQlt.le) fun hEq ↦ hQlt.ne ?_
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p.asIdeal)
          Ideal.Quotient.mk_surjective Q, hEq,
        Ideal.map_comap_of_surjective (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective]
    -- there is no such prime, so `Q` is the zero ideal
    have heq : Q.comap (Ideal.Quotient.mk p.asIdeal) = p.asIdeal :=
      ((hmk Q).lt_or_eq.resolve_left fun hc ↦ h.2
        ((PrimeSpectrum.asIdeal_lt_asIdeal p ⟨_, hQc⟩).mp hc)
        ((PrimeSpectrum.asIdeal_lt_asIdeal ⟨_, hQc⟩ q).mp hlt)).symm
    have hbot : Q = ⊥ := by
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p.asIdeal)
        Ideal.Quotient.mk_surjective Q, heq, Ideal.map_quotient_self]
    simp [hbot, Ideal.height_bot]
  · rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hbot
    rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcomap
    exact ((PrimeSpectrum.asIdeal_lt_asIdeal p q).mpr h.lt).ne hcomap

/-- For a prime `p` of a commutative ring `R` we always have `height p + dim (R ⧸ p) ≤ dim R`:
a chain of primes below `p` and a chain of primes above `p` concatenate. The reverse inequality
is a genuine restriction on `R`; see `Ideal.height_add_ringKrullDim_quotient` for the case of a
finitely generated domain over a field. -/
theorem Ideal.height_add_ringKrullDim_quotient_le (p : Ideal R) [hp : p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  have : Nonempty (PrimeSpectrum R) := ⟨⟨p, hp⟩⟩
  rw [ringKrullDim_quotient_eq_coheight,
    PrimeSpectrum.height_eq_orderHeight (⟨p, hp⟩ : PrimeSpectrum R), ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact_mod_cast le_iSup (fun x : PrimeSpectrum R ↦ Order.height x + Order.coheight x) _
