/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.QuotSMulTop
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-!
# Good elements for a maximal regular sequence

A good element for a maximal regular sequence on a finite Cohen–Macaulay module over a
Noetherian local ring is a nonzerodivisor, and the quotient is again Cohen–Macaulay.

## Implementation details

Dimension uses the inherited prime-ideal inclusion order, including negative infinity for the
empty set. The proof is by induction on the dimension. In dimension one, a nonzero kernel of
multiplication by `g` would have the maximal ideal as an associated prime, contradicting
regularity of `f₁`; this replaces the finite-length argument of the source. In the inductive
step one passes to `M/f₁M` and permutes the regular pair `f₁, g`.

## References

* [Stacks, Tag 00N4]
* [Stacks, Tag 00N2]
* [Stacks, Tag 00N3]
-/

@[expose] public section

universe u v

namespace Module

private theorem regular_of_zero_dim_intersection {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] {f g : R}
    (hf : f ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M f)
    (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim ((support R M ∩ PrimeSpectrum.zeroLocus {g}) :
      Set (PrimeSpectrum R)) = 0) : IsSMulRegular M g := by
  classical
  by_contra hn
  have hu : g ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨p, hp, hgp⟩ := Set.mem_iUnion₂.mp hu
  let q : PrimeSpectrum R := ⟨p, hp.isPrime⟩
  have hqs : q ∈ support R M := mem_support_iff_of_finite.mpr (by
    simpa only [Submodule.annihilator_top] using hp.annihilator_le)
  have hq : q ∈ support R M ∩ PrimeSpectrum.zeroLocus {g} :=
    ⟨hqs, by simpa [PrimeSpectrum.mem_zeroLocus] using hgp⟩
  let m : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  have hqm : q ≤ m := IsLocalRing.le_maximalIdeal hp.isPrime.ne_top
  have hm : m ∈ support R M ∩ PrimeSpectrum.zeroLocus {g} :=
    ⟨mem_support_mono hqm hqs, by
      simpa [PrimeSpectrum.mem_zeroLocus] using (show g ∈ m.asIdeal from hg)⟩
  have he : q = m := by
    have hmax := (Order.krullDim_nonpos_iff_forall_isMax.mp hdim.le) ⟨q, hq⟩
    have hmq : (⟨m, hm⟩ : ↥(support R M ∩ PrimeSpectrum.zeroLocus {g})) ≤ ⟨q, hq⟩ :=
      hmax (show (⟨q, hq⟩ : ↥(support R M ∩ PrimeSpectrum.zeroLocus {g})) ≤ ⟨m, hm⟩ from hqm)
    exact le_antisymm hqm hmq
  have hfp : f ∈ p := by
    change f ∈ q.asIdeal
    rw [he]
    exact hf
  have huf : f ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
    Set.mem_iUnion₂.mpr ⟨p, hp, hfp⟩
  rw [biUnion_associatedPrimes_eq_compl_regular] at huf
  exact huf hreg

private theorem good_sequence_regular {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (fs : List R) (hlen : fs.length = n + 1)
    (hmem : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hgood : ∀ i : ℕ, i < n + 1 →
      Order.krullDim ((support R M ∩
        PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i}) : Set (PrimeSpectrum R)) =
          (((n + 1 - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular M (g :: fs.take n) := by
  induction n generalizing M fs with
  | zero =>
    cases fs with
    | nil => simp at hlen
    | cons f fs =>
      have hf := (RingTheory.Sequence.isRegular_cons_iff M f fs).mp hreg
      have hgdim : Order.krullDim ((support R M ∩ PrimeSpectrum.zeroLocus {g}) :
          Set (PrimeSpectrum R)) = 0 := by
        have hs : {x : R | x ∈ g :: (f :: fs).take 0} = {g} := by ext x; simp
        have hz := hgood 0 (by omega)
        rw [hs] at hz
        simpa using hz
      have hgreg := regular_of_zero_dim_intersection M (hmem f (by simp)) hf.1 hg hgdim
      let := nontrivial_quotSMulTop_of_mem_maximalIdeal M hg
      simpa using (RingTheory.Sequence.IsRegular.nil R (QuotSMulTop g M)).cons hgreg
  | succ n ih =>
    cases fs with
    | nil => simp at hlen
    | cons f fs =>
      have hf := (RingTheory.Sequence.isRegular_cons_iff M f fs).mp hreg
      let := hf.2.nontrivial
      have hgood' : ∀ j : ℕ, j < n + 1 →
          Order.krullDim ((support R (QuotSMulTop f M) ∩
            PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take j}) :
              Set (PrimeSpectrum R)) =
            (((n + 1 - j - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        intro j hj
        have hset : support R (QuotSMulTop f M) ∩
            PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take j} =
            support R M ∩
              PrimeSpectrum.zeroLocus {x : R | x ∈ g :: (f :: fs).take (j + 1)} := by
          rw [support_quotSMulTop]
          ext p
          simp only [List.take_succ_cons, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
            Set.subset_def, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
          aesop
        rw [hset]
        convert hgood (j + 1) (by omega) using 1
        congr 2
        omega
      have htail := ih (QuotSMulTop f M) fs (by simpa using hlen)
        (fun x hx ↦ hmem x (by simp [hx])) hf.2 hgood'
      have hfg : RingTheory.Sequence.IsRegular M (f :: g :: fs.take n) :=
        htail.cons hf.1
      have hgf := IsLocalRing.isRegular_of_perm hfg (List.Perm.swap g f (fs.take n))
      simpa using hgf

/-- A good element for a maximal regular sequence on a nonzero finite Cohen–Macaulay
module of positive dimension is regular; its quotient is Cohen–Macaulay of dimension
one less, with the indicated initial segment as a maximal regular sequence.

Here `fs` lists `f₁, …, f_d`. Cohen–Macaulayness is written as equality of depth
and support dimension. Goodness is the displayed dimension condition on the support
intersected with the zero locus of `g :: fs.take i`. -/
theorem isSMulRegular_of_good_sequence {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (d : ℕ) (hd : 1 ≤ d)
    (hcm : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (hdim : supportDim R M = ((d : ℕ∞) : WithBot ℕ∞))
    (fs : List R) (hlen : fs.length = d)
    (hmem : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hgood : ∀ i : ℕ, i < d →
      Order.krullDim ((Module.support R M ∩
        PrimeSpectrum.zeroLocus {x : R | x ∈ g :: fs.take i}) : Set (PrimeSpectrum R)) =
          (((d - i - 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    IsSMulRegular M g ∧
      (IsLocalRing.depth (R := R) (QuotSMulTop g M) : WithBot ℕ∞) =
        supportDim R (QuotSMulTop g M) ∧
      IsLocalRing.depth (R := R) (QuotSMulTop g M) = (d - 1 : ℕ) ∧
      supportDim R (QuotSMulTop g M) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop g M) (fs.take (d - 1)) := by
  -- Record the original depth; the induction itself only needs regularity and goodness.
  have _hdepthM := hcm.trans hdim
  have he : d - 1 + 1 = d := by omega
  have hfull := good_sequence_regular (d - 1) M fs (by omega) hmem hreg g hg
    (by simpa only [he] using hgood)
  obtain ⟨hgreg, hqreg⟩ :=
    (RingTheory.Sequence.isRegular_cons_iff M g (fs.take (d - 1))).mp hfull
  let := hqreg.nontrivial
  have hqdim : supportDim R (QuotSMulTop g M) =
      (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [supportDim, support_quotSMulTop]
    have hs : {x : R | x ∈ g :: fs.take 0} = {g} := by ext x; simp
    have hz := hgood 0 (by omega)
    rw [hs] at hz
    simpa using hz
  have hupper : IsLocalRing.depth (R := R) (QuotSMulTop g M) ≤ ((d - 1 : ℕ) : ℕ∞) :=
    WithBot.coe_le_coe.mp ((IsLocalRing.depth_le_supportDim (QuotSMulTop g M)).trans_eq
      hqdim)
  have hlower : ((d - 1 : ℕ) : ℕ∞) ≤ IsLocalRing.depth (R := R) (QuotSMulTop g M) := by
    unfold IsLocalRing.depth Ideal.depth
    split
    · exact le_top
    · apply le_sSup
      refine ⟨fs.take (d - 1), hqreg, ?_, ?_⟩
      · exact fun x hx ↦ hmem x (List.mem_of_mem_take hx)
      · simp [List.length_take, hlen]
  have hdepth := le_antisymm hupper hlower
  exact ⟨hgreg, by rw [hdepth, hqdim], hdepth, hqdim, hqreg⟩

end Module
