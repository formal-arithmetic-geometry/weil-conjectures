/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Support

/-!
# Prime avoidance for a good element and a prescribed parameter

Prime avoidance supplies an element that is good for a given maximal regular sequence and
also cuts the support modulo a prescribed parameter.

## Implementation details

The element is chosen in the maximal ideal outside the finitely many minimal primes of the
supports after the first `i` regular elements and of `Supp(M) ∩ V(g)`; none of these is the
maximal ideal, since all these supports have positive dimension. Intersecting with `V(x)`
then drops each dimension by exactly one. No regularity of `x` or Cohen-Macaulayness of its
quotient is used.

## References

* [Stacks, Tag 00N5]
* [Stacks, Tag 00DS]
-/

@[expose] public section

universe u v

namespace Module

private theorem maximal_not_minimal_of_supportDim_pos
    {R : Type u} [CommRing R] [IsLocalRing R]
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hpos : (0 : WithBot ℕ∞) < supportDim R N) :
    IsLocalRing.maximalIdeal R ∉ (annihilator R N).minimalPrimes := by
  intro hm
  have heq : ∀ p : support R N, p.val.asIdeal = IsLocalRing.maximalIdeal R := by
    intro p
    have hpm := IsLocalRing.le_maximalIdeal p.val.isPrime.ne_top
    exact le_antisymm hpm (hm.2
      ⟨p.val.isPrime, (mem_support_iff_of_finite.mp p.property)⟩ hpm)
  have : Subsingleton (support R N) := ⟨fun p q ↦
    Subtype.ext (PrimeSpectrum.ext (by rw [heq p, heq q]))⟩
  exact (not_lt_of_ge (Order.krullDim_nonpos_of_subsingleton (α := support R N))) hpos

private theorem exists_avoid_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (s : Finset (Ideal R))
    (hmax : ∀ I ∈ s, IsLocalRing.maximalIdeal R ∉ I.minimalPrimes) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
      ∀ I ∈ s, ∀ p ∈ I.minimalPrimes, x ∉ p := by
  classical
  let ps : Set (Ideal R) := ⋃ I ∈ s, I.minimalPrimes
  have hfin : ps.Finite := s.finite_toSet.biUnion
    (fun I _ ↦ I.finite_minimalPrimes_of_isNoetherianRing)
  have hprime : ∀ p ∈ hfin.toFinset, p.IsPrime := by
    intro p hp
    have hps : p ∈ ps := hfin.mem_toFinset.mp hp
    obtain ⟨I, hI, hpI⟩ := Set.mem_iUnion₂.mp hps
    exact hpI.1.1
  have hnsub : ¬ (IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (hfin.toFinset : Set (Ideal R)), (p : Set R) := by
    intro hs
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) ⊥
      (fun p hp _ _ ↦ hprime p hp)).mp hs
    obtain ⟨I, hI, hpI⟩ := Set.mem_iUnion₂.mp (hfin.mem_toFinset.mp hp)
    have hpm := IsLocalRing.le_maximalIdeal (hprime p hp).ne_top
    have heq : p = IsLocalRing.maximalIdeal R := le_antisymm hpm hmp
    exact hmax I hI (heq ▸ hpI)
  obtain ⟨x, hx, hxout⟩ := Set.not_subset.mp hnsub
  refine ⟨x, hx, ?_⟩
  intro I hI p hp hxp
  apply hxout
  exact Set.mem_iUnion₂.mpr ⟨p, hfin.mem_toFinset.mpr
    (Set.mem_iUnion₂.mpr ⟨I, hI, hp⟩), hxp⟩

/-- Prime avoidance supplies an element good for a given maximal regular sequence
which also cuts the support modulo a prescribed parameter. -/
theorem exists_good_element_cutting_parameter
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (n : ℕ) (hM : supportDim R M = (((n + 2 : ℕ) : ℕ∞) : WithBot ℕ∞))
    (fs : List R) (hlen : fs.length = n + 2)
    (hmem : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs)
    (g : R)
    (hcut : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
      (∀ i : ℕ, i < n + 2 →
        Order.krullDim (support R M ∩
          PrimeSpectrum.zeroLocus {r : R | r ∈ x :: fs.take i} : Set (PrimeSpectrum R)) =
            (((n + 2 - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) ∧
      Order.krullDim (support R (QuotSMulTop x M) ∩
        PrimeSpectrum.zeroLocus ({g} : Set R) : Set (PrimeSpectrum R)) =
          (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  classical
  let Q (i : Fin (n + 2)) := M ⧸ (Ideal.ofList (fs.take i.val) • ⊤ : Submodule R M)
  have hQdim : ∀ i : Fin (n + 2),
      supportDim R (Q i) = (((n + 2 - i.val : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro i
    have hmemi : ∀ f ∈ fs.take i.val, f ∈ IsLocalRing.maximalIdeal R :=
      fun f hf ↦ hmem f (List.mem_of_mem_take hf)
    have hweak : RingTheory.Sequence.IsWeaklyRegular M (fs.take i.val) :=
      ((RingTheory.Sequence.isWeaklyRegular_append_iff M (fs.take i.val)
        (fs.drop i.val)).mp (by simpa using hreg.toIsWeaklyRegular)).1
    have hregi := RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      M hmemi hweak
    have heq := supportDim_add_length_eq_supportDim_of_isRegular (fs.take i.val) hregi
    have hleni : (fs.take i.val).length = i.val := by
      simp only [List.length_take, hlen, min_eq_left (by omega : i.val ≤ n + 2)]
    rw [hleni, hM] at heq
    apply (ENat.WithBot.add_natCast_cancel (c := i.val)).mp
    calc
      supportDim R (Q i) + i.val = (((n + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := heq
      _ = (((n + 2 - i.val : ℕ) : ℕ∞) : WithBot ℕ∞) + i.val := by
        norm_cast
        omega
  let A (i : Fin (n + 2)) := annihilator R (Q i)
  let G := annihilator R (QuotSMulTop g M)
  let s : Finset (Ideal R) := insert G (Finset.univ.image A)
  have hGdim : supportDim R (QuotSMulTop g M) =
      (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [supportDim, support_quotSMulTop]
    exact hcut
  have hmax : ∀ I ∈ s, IsLocalRing.maximalIdeal R ∉ I.minimalPrimes := by
    intro I hI
    rcases Finset.mem_insert.mp hI with rfl | hI
    · apply maximal_not_minimal_of_supportDim_pos (QuotSMulTop g M)
      rw [hGdim]
      norm_cast
      omega
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
      apply maximal_not_minimal_of_supportDim_pos (Q i)
      rw [hQdim]
      norm_cast
      omega
  obtain ⟨x, hx, havoid⟩ := exists_avoid_minimalPrimes s hmax
  refine ⟨x, hx, ?_, ?_⟩
  · intro i hi
    let j : Fin (n + 2) := ⟨i, hi⟩
    have hdrop := supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
      (M := Q j) (havoid (A j) (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ j, rfl⟩))) hx
    have heq : (support R M ∩
        PrimeSpectrum.zeroLocus {r : R | r ∈ x :: fs.take i} : Set (PrimeSpectrum R)) =
        support R (QuotSMulTop x (Q j)) := by
      rw [support_quotSMulTop, support_quotient, Ideal.ofList, PrimeSpectrum.zeroLocus_span]
      ext p
      simp only [Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
        Set.mem_ofPred_eq, List.mem_cons, Set.mem_singleton_iff]
      aesop
    rw [heq]
    change supportDim R (QuotSMulTop x (Q j)) = _
    apply ENat.WithBot.add_one_cancel.mp
    rw [hdrop, hQdim]
    norm_cast
    dsimp [j]
    omega
  · have hdrop := supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
      (M := QuotSMulTop g M) (havoid G (Finset.mem_insert_self _ _)) hx
    have heq : (support R (QuotSMulTop x M) ∩
        PrimeSpectrum.zeroLocus ({g} : Set R) : Set (PrimeSpectrum R)) =
        support R (QuotSMulTop x (QuotSMulTop g M)) := by
      rw [support_quotSMulTop, support_quotSMulTop, support_quotSMulTop]
      ext p
      simp only [Set.mem_inter_iff]
      tauto
    rw [heq]
    change supportDim R (QuotSMulTop x (QuotSMulTop g M)) = _
    apply ENat.WithBot.add_one_cancel.mp
    rw [hdrop, hGdim]
    simp


end Module
