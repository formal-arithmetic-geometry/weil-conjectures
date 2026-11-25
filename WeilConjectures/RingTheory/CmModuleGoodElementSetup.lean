/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsSMulRegularOfGoodSequence
import WeilConjectures.RingTheory.GoodElementCuttingParameter
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Support

/-!
# Regular sequences adapted to a cutting element on a Cohen--Macaulay module

For a finite Cohen--Macaulay module `M` over a noetherian local ring and an element `g` of the
maximal ideal cutting the support dimension by one, we construct a maximal `M`-regular sequence
`fs` such that each `g :: fs.take i` cuts the support dimension exactly
(`Module.exists_good_sequence_for_cm_element`). This is the data used by
`isSMulRegular_of_good_sequence`.

## Implementation details

The depth is a natural number `d` by finiteness of the Krull dimension, and `d ≥ 1` since
`M / g M` is nonzero by Nakayama. The proof inducts on `d`: for `d ≥ 2`, prime avoidance gives
an element `x` good for a regular sequence of length `d` and cutting the support modulo `g`;
`M / x M` is Cohen--Macaulay of dimension `d - 1`, and `x` is prepended to the adapted sequence
obtained there.

## References

* [Stacks, Tag 00N5]
* [Stacks, Tag 00N4]
-/

@[expose] public section

universe u v

namespace Module

private theorem exists_sequence_of_depth_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞)) :
    ∃ fs : List R, fs.length = d ∧
      (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular M fs := by
  classical
  have hm : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hdef : IsLocalRing.depth (R := R) M = sSup {k : ℕ∞ | ∃ fs : List R,
      RingTheory.Sequence.IsRegular M fs ∧
      (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧ k = (fs.length : ℕ∞)} := by
    simp only [IsLocalRing.depth, Ideal.depth, ite_eq_right hm]
  have hempty : RingTheory.Sequence.IsRegular (R := R) M [] := by
    simp [RingTheory.Sequence.isRegular_iff]
  let : Nonempty {k : ℕ∞ | ∃ fs : List R, RingTheory.Sequence.IsRegular M fs ∧
      (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧ k = (fs.length : ℕ∞)} :=
    ⟨⟨0, [], hempty, by simp, rfl⟩⟩
  have hsup := ENat.sSup_mem_of_nonempty_of_lt_top (s := {k : ℕ∞ | ∃ fs : List R,
    RingTheory.Sequence.IsRegular M fs ∧
    (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧ k = (fs.length : ℕ∞)})
    (by rw [← hdef, hdepth]; simp)
  rw [← hdef, hdepth] at hsup
  obtain ⟨fs, hreg, hmem, hlen⟩ := hsup
  refine ⟨fs, ?_, hmem, hreg⟩
  exact_mod_cast hlen.symm

private theorem exists_adapted_sequence_of_dimension
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] (hd : 1 ≤ d)
    (hdepth : IsLocalRing.depth (R := R) M = (d : ℕ∞))
    (hM : supportDim R M = (((d : ℕ∞) : WithBot ℕ∞)))
    (g : R)
    (hcut : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∃ fs : List R, fs.length = d ∧
      (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular M fs ∧
      (∀ i : ℕ, i < d →
        Order.krullDim (support R M ∩
          PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i} : Set (PrimeSpectrum R)) =
            (((d - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) := by
  induction d generalizing M with
  | zero => omega
  | succ d ih =>
    obtain ⟨fs, hlen, hmem, hreg⟩ := exists_sequence_of_depth_eq M (d + 1) hdepth
    cases d with
    | zero =>
      refine ⟨fs, hlen, hmem, hreg, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      have hset : {x : R | x ∈ g :: fs.take 0} = {g} := by ext r; simp
      rw [hset]
      simpa using hcut
    | succ n =>
      have hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M := by
        rw [hdepth, hM]
      obtain ⟨x, hx, hxgood, hxcut⟩ := exists_good_element_cutting_parameter
        M n hM fs hlen hmem hreg g (by simpa using hcut)
      obtain ⟨hxreg, _, hQdepth, hQdim, _⟩ :=
        isSMulRegular_of_good_sequence M (n + 2) (by omega) hCM hM
          fs hlen hmem hreg x hx hxgood
      let : Nontrivial (QuotSMulTop x M) :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
      obtain ⟨qs, hqlen, hqmem, hqreg, hqgood⟩ := ih (QuotSMulTop x M)
        (by omega) (by simpa using hQdepth) (by simpa using hQdim)
        (by simpa using hxcut)
      refine ⟨x :: qs, by simp [hqlen], ?_, ?_, ?_⟩
      · simpa using And.intro hx hqmem
      · exact (RingTheory.Sequence.isRegular_cons_iff M x qs).mpr ⟨hxreg, hqreg⟩
      · intro i hi
        cases i with
        | zero =>
          have hset : {r : R | r ∈ g :: (x :: qs).take 0} = {g} := by ext r; simp
          rw [hset]
          simpa using hcut
        | succ j =>
          have heq : (support R M ∩
              PrimeSpectrum.zeroLocus {r : R | r ∈ g :: (x :: qs).take (j + 1)} :
                Set (PrimeSpectrum R)) =
              support R (QuotSMulTop x M) ∩
                PrimeSpectrum.zeroLocus {r : R | r ∈ g :: qs.take j} := by
            ext p
            simp only [support_quotSMulTop, List.take_succ_cons, Set.mem_inter_iff,
              PrimeSpectrum.mem_zeroLocus, Set.subset_def, Set.mem_ofPred_eq,
              Set.mem_singleton_iff, List.mem_cons]
            aesop
          rw [heq]
          simpa [Nat.succ_eq_add_one, Nat.sub_sub] using hqgood j (by omega)

/-- If `M` is a finite Cohen--Macaulay module and `g` in the maximal ideal cuts the support
dimension by one, then the support dimension is some `d ≥ 1` and there is an `M`-regular sequence
`fs` of length `d` in the maximal ideal such that the support of `M` cut by `g :: fs.take i` has
dimension `d - i - 1` for every `i < d`. -/
theorem exists_good_sequence_for_cm_element
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) + 1 = supportDim R M) :
    ∃ d : ℕ, 1 ≤ d ∧ supportDim R M = (((d : ℕ∞) : WithBot ℕ∞)) ∧
      ∃ fs : List R, fs.length = d ∧
        (∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M fs ∧
        (∀ i : ℕ, i < d →
          Order.krullDim ((support R M ∩
            PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i}) :
              Set (PrimeSpectrum R)) =
            (((d - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) := by
  have hfinite : IsLocalRing.depth (R := R) M ≠ ⊤ := by
    intro heq
    have hbound := supportDim_le_ringKrullDim R M
    rw [← hCM, heq] at hbound
    exact (ne_of_lt (ringKrullDim_lt_top (R := R))) (by simpa using hbound)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hM : supportDim R M = (((d : ℕ∞) : WithBot ℕ∞)) := by rw [← hCM, ← hd]
  let : Nontrivial (QuotSMulTop g M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M hg
  have hcut_nonneg : (0 : WithBot ℕ∞) ≤ Order.krullDim
      (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) : Set (PrimeSpectrum R)) := by
    have : Nonempty (support R (QuotSMulTop g M)) :=
      nonempty_support_of_nontrivial.to_subtype
    have hn := Order.krullDim_nonneg (α := support R (QuotSMulTop g M))
    rw [support_quotSMulTop] at hn
    exact hn
  have hpos : 1 ≤ d := by
    have hbound : (1 : WithBot ℕ∞) ≤ Order.krullDim
        (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) : Set (PrimeSpectrum R)) + 1 :=
      by simpa only [zero_add] using add_le_add hcut_nonneg (le_refl (1 : WithBot ℕ∞))
    rw [hdim, hM] at hbound
    exact_mod_cast (show (1 : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) by
      simpa using hbound)
  have hcut : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    apply ENat.WithBot.add_one_cancel.mp
    rw [hdim, hM]
    have hsucc : d - 1 + 1 = d := by omega
    simpa only [Nat.cast_add, Nat.cast_one, WithBot.coe_add,
      WithBot.coe_one] using congrArg (fun k : ℕ ↦ ((k : ℕ∞) : WithBot ℕ∞)) hsucc.symm
  refine ⟨d, hpos, hM, ?_⟩
  exact exists_adapted_sequence_of_dimension d M hpos hd.symm hM g hcut

end Module
