/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The induced map on completions of prime localizations

For a prime `q` of `S` over `p` in `R`, the local map `R_p → S_q` induces a map of completions
at the maximal ideals.

## Implementation details

The map is obtained from `AdicCompletion.liftRingHom` applied to the induced maps on the
quotients by powers of the maximal ideals. No finiteness hypothesis is needed.

## References

* [Stacks, Tag 07NC], the natural map
-/

@[expose] public section

universe u v

namespace Algebra

/-- The local map `R_p → S_q` induces a ring map on completions at the maximal ideals,
compatible with the local map at every finite level. -/
theorem exists_completion_map_atPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    ∃ ψ : Rph →+* Sqh,
      ∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a) := by
  dsimp only
  let p : Ideal R := q.comap (algebraMap R S)
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let Ip := IsLocalRing.maximalIdeal Rp
  let Iq := IsLocalRing.maximalIdeal Sq
  let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  have hmap : Ip.map f ≤ Iq := IsLocalRing.map_maximalIdeal_le f
  have hpow (n : ℕ) : (Ip ^ n).map f ≤ Iq ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  let qmap (n : ℕ) : Rp ⧸ Ip ^ n →+* Sq ⧸ Iq ^ n :=
    Ideal.quotientMap (Iq ^ n) f (Ideal.map_le_iff_le_comap.mp (hpow n))
  let F (n : ℕ) := (qmap n).comp (AdicCompletion.evalₐ Ip n).toRingHom
  have hF {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow Iq hmn).comp (F n) = F m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [F, qmap] using
        congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk Ip hmn x)
  refine ⟨AdicCompletion.liftRingHom Iq F (fun hmn ↦ hF hmn), ?_⟩
  intro n x a hx
  rw [AdicCompletion.evalₐ_liftRingHom]
  change qmap n (AdicCompletion.evalₐ Ip n x) = _
  rw [hx]
  exact Ideal.quotientMap_mk

end Algebra
