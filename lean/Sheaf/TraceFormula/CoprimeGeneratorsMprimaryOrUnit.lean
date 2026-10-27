/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.UFD
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-!
# Coprime generators in a regular local surface

Source: Stacks Project, Curves, Tag 0C48, proof of
`lemma-reduced-quotient-regular-ring-dim-2` (blueprint:
`lem-trf-coprime-generators-mprimary-or-unit`).
-/

@[expose] public section

universe u

namespace RingTheory

/-- Let `(A, 𝔫)` be a regular local ring of Krull dimension two.  If a finite
family of elements has no common nonunit divisor, its generated ideal is the
unit ideal or has radical the maximal ideal.

Source: Stacks Project, Curves, Tag 0C48, proof of
`lemma-reduced-quotient-regular-ring-dim-2`, the paragraph beginning
“Thus the gcd of g_1, ..., g_r is 1”.

Proof. The regular-local UFD statement
`lem-trf-regular-local-ufd-boundary-factorization` gives that `A` is a
Noetherian domain and a UFD.  If the generated ideal is proper, every prime
above it is contained in the maximal ideal.  A nonmaximal such prime has
height one by the dimension-two prime-chain argument, hence is principal by
`lem-trf-ufd-height-one`; its generator would be a common divisor and thus a
unit, a contradiction.  The maximal ideal is therefore the only prime above
the generated ideal, and `PrimeSpectrum.zeroLocus_eq_iff` together with the
radical/intersection description gives the stated radical equality.
(blueprint: lem-trf-coprime-generators-mprimary-or-unit)
-/
theorem coprimeGeneratorsMprimaryOrUnit
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = (2 : WithBot ℕ∞))
    (r : ℕ) (g : Fin r → A)
    (hdiv : ∀ d : A, (∀ i : Fin r, d ∣ g i) → IsUnit d) :
    Ideal.span (Set.range g) = ⊤ ∨
      (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal A := by
  classical
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨s, hcard, hs⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  have ht : IsLocalRing.IsRegularSystemOfParameters s.toList := by
    constructor
    · simpa [m] using hs
    · rw [Finset.length_toList, hcard, IsRegularLocalRing.spanFinrank_maximalIdeal]
  have hufd := regularLocalUFDBoundaryFactorization A s.toList ht 0
    (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
  let : UniqueFactorizationMonoid A := hufd.2.1
  let J := Ideal.span (Set.range g)
  by_cases htop : J = ⊤
  · exact Or.inl htop
  right
  have hJ0 : J ≠ ⊥ := by
    intro hzero
    have hu := hdiv 0 fun i ↦ by
      apply zero_dvd_iff.mpr
      have hi : g i ∈ J := Ideal.subset_span (Set.mem_range_self i)
      simpa [hzero] using hi
    exact not_isUnit_zero hu
  have hprime (p : Ideal A) [p.IsPrime] (hJp : J ≤ p) : p = m := by
    by_contra hpm
    have hlt : p < m := lt_of_le_of_ne
      (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hpm
    have hmheight : m.height = (2 : ℕ∞) := by
      have hm : (m.height : WithBot ℕ∞) = 2 :=
        (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans hdim
      exact WithBot.coe_injective hm
    have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hmheight] at hheight
    have hle : p.height ≤ 1 := by
      apply ENat.lt_two_iff.mp
      exact (ENat.add_one_le_iff' (by simp)).mp hheight
    have hp0 : p ≠ ⊥ := fun hp ↦ hJ0 (bot_unique (hp ▸ hJp))
    have hheight1 : p.height = 1 := le_antisymm hle
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp0))
    obtain ⟨a, ha⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight1
    change p = Ideal.span {a} at ha
    have hua : IsUnit a := hdiv a fun i ↦ Ideal.mem_span_singleton.mp
      (ha ▸ hJp (Ideal.subset_span (Set.mem_range_self i)))
    exact Ideal.IsPrime.ne_top ‹_› (ha.trans (Ideal.span_singleton_eq_top.mpr hua))
  apply le_antisymm
  · exact (inferInstance : m.IsPrime).radical_le_iff.mpr
      (IsLocalRing.le_maximalIdeal htop)
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro p ⟨hJp, hp⟩
    let := hp
    exact (hprime p hJp).symm.le

end RingTheory
