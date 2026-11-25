/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Submodule

/-!
# Uniform containment of local maximal-ideal powers

For `S` finite over a Noetherian ring `R` and a prime `p`, one positive exponent `c` satisfies
`N_q^c ⊆ m S_q` for all primes `q` of `S` over `p`, where `N_q` is the maximal ideal of `S_q`.

## Implementation details

The closed fibre of `R_p ⊗_R S` is Artinian with finitely many primes, corresponding to the `q`.
Each `S_q/m S_q` is Artinian local, so `m S_q` has radical `N_q`, and some power of the finitely
generated `N_q` lies in `m S_q`. Take the maximum of these exponents and one.

## References

* [Stacks, Tag 0394] (radical-power argument)
* [Stacks, Tag 07N9] (finite fibre)
-/

@[expose] public section

universe u v
namespace AdicCompletion

/-- One positive exponent works for all primes over a fixed base prime. -/
theorem local_tensor_quotient_power_bound
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∃ c : ℕ, 1 ≤ c ∧ ∀ q : p.primesOver S,
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ c ≤
        m.map (Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p))) := by
  classical
  dsimp
  let : Fintype (p.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hpoint : ∀ q : p.primesOver S, ∃ c : ℕ, 1 ≤ c ∧
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ c ≤
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
          (Localization.localRingHom p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p))) := by
    intro q
    let T := Localization.AtPrime q.1
    let f := Localization.localRingHom p q.1 (algebraMap R S)
      (Ideal.LiesOver.over (P := q.1) (p := p))
    have hcomp : f.comp (algebraMap R (Localization.AtPrime p)) =
        (algebraMap S T).comp (algebraMap R S) := by
      ext x
      exact Localization.localRingHom_to_map p q.1 (algebraMap R S)
        (Ideal.LiesOver.over (P := q.1) (p := p)) x
    have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map f =
        (p.map (algebraMap R S)).map (algebraMap S T) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, Ideal.map_map]
    have hmin : q.1 ∈ (p.map (algebraMap R S)).minimalPrimes := by
      simpa only [← Ideal.over_def q.1 p] using
        (Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) q.1)
    have hrad : ((p.map (algebraMap R S)).map (algebraMap S T)).radical =
        IsLocalRing.maximalIdeal T := by
      rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := T) q.1 _ hmin,
        IsLocalization.AtPrime.map_eq_maximalIdeal q.1 T]
    let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    have hfg : (IsLocalRing.maximalIdeal T).FG := Ideal.fg_of_isNoetherianRing _
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (le_of_eq hrad.symm) hfg
    refine ⟨max 1 n, le_max_left _ _, ?_⟩
    change (IsLocalRing.maximalIdeal T) ^ max 1 n ≤ _
    rw [hmap]
    exact (Ideal.pow_le_pow_right (le_max_right 1 n)).trans hn
  choose c _ hc using hpoint
  obtain ⟨n, hn⟩ := (Set.finite_range c).bddAbove
  refine ⟨max 1 n, le_max_left _ _, ?_⟩
  intro q
  exact (Ideal.pow_le_pow_right ((hn (Set.mem_range_self q)).trans
    (le_max_right 1 n))).trans (hc q)

end AdicCompletion
