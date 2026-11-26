/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.AnnihilatorElementFlatBaseChange
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.FlatLocalDepthReduction
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Depth formula for a flat local homomorphism

For a flat local homomorphism `R → S` of Noetherian local rings, the closed fibre
`S / m_R S` is a Noetherian local ring and `depth S = depth R + depth (S / m_R S)`.

## Implementation details

The proof inducts on `n = depth R + depth (S / m_R S)`, uniformly over flat local maps.
In depth zero, elements annihilated exactly by the maximal ideals of `R` and of the fibre
combine to an element of `S` annihilated by `m_S`. If the fibre has positive depth, a lifted
fibre nonzerodivisor `f` is a nonzerodivisor on `S` with `S / f S` flat over `R`; otherwise a
nonzerodivisor `f ∈ m_R` gives the flat local map `R / f R → S / f S` with the same fibre.
In both cases the depths drop by one and induction applies. The addition is in `ℕ∞`.

## References

* [Stacks, Tag 0337]
* [Stacks, Tag 0338]
* [EGA IV, Proposition 6.3.1]
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem depth_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : depth (R := A) A ≠ ⊤ := by
  have h := depth_le_supportDim (R := A) A
  rw [Module.supportDim_self_eq_ringKrullDim] at h
  intro ht
  rw [ht] at h
  exact ringKrullDim_ne_top (R := A) (top_le_iff.mp h)

private theorem exists_annihilator_of_depth_zero (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hd : depth (R := A) A = 0) :
    ∃ z : A, ∀ a : A, a * z = 0 ↔ a ∈ maximalIdeal A := by
  have hm : maximalIdeal A ∈ associatedPrimes A A := by
    by_contra hm
    obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective A A hm
    have hmem : ∀ a ∈ ([x] : List A), a ∈ maximalIdeal A := by simpa using hx
    have hseq : RingTheory.Sequence.IsRegular A [x] :=
      (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
        (RingTheory.Sequence.IsWeaklyRegular.cons hreg
          (RingTheory.Sequence.IsWeaklyRegular.nil A (QuotSMulTop x A)))
    have hlen : (1 : ℕ∞) ≤ depth (R := A) A := by
      unfold depth Ideal.depth
      split_ifs with h
      · exact le_top
      · apply le_sSup
        exact ⟨[x], hseq, hmem, by simp⟩
    rw [hd] at hlen
    exact (by decide : ¬ (1 : ℕ∞) ≤ 0) hlen
  obtain ⟨_, z, hz⟩ := (isAssociatedPrime_iff.mp hm)
  refine ⟨z, fun a ↦ ?_⟩
  rw [hz]
  simp [Submodule.mem_colon_singleton, smul_eq_mul]

private theorem depth_zero_of_annihilator (A : Type*) [CommRing A] [IsLocalRing A]
    (z : A) (hz : ∀ a : A, a * z = 0 ↔ a ∈ maximalIdeal A) :
    depth (R := A) A = 0 := by
  have hzne : z ≠ 0 := by
    intro h
    have : (1 : A) ∈ maximalIdeal A := (hz 1).mp (by simp [h])
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  unfold depth Ideal.depth
  have hm : (maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using (maximalIdeal.isMaximal A).ne_top
  rw [ite_eq_right hm]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hinj := ((RingTheory.Sequence.isRegular_cons_iff A x xs).mp hreg).1
    have hxz : x • z = 0 := (hz x).mpr (hmem x (by simp))
    exact (hzne (hinj (hxz.trans (smul_zero x).symm))).elim

private theorem depth_zero_of_flat_local {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (hflat : φ.Flat)
    [IsLocalRing (B ⧸ (maximalIdeal A).map φ)]
    (hA : depth (R := A) A = 0)
    (hF : depth (R := B ⧸ (maximalIdeal A).map φ)
      (B ⧸ (maximalIdeal A).map φ) = 0) : depth (R := B) B = 0 := by
  let I := (maximalIdeal A).map φ
  obtain ⟨z, hz⟩ := exists_annihilator_of_depth_zero A hA
  obtain ⟨ybar, hy⟩ := exists_annihilator_of_depth_zero (B ⧸ I) hF
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  have hann : Module.annihilator B (Ideal.span ({φ z} : Set B)) = I := by
    rw [φ.annihilator_element_flat_base_change hflat z]
    congr 1
    ext a
    change a ∈ (Ideal.span ({z} : Set A)).annihilator ↔ a ∈ maximalIdeal A
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using hz a
  apply depth_zero_of_annihilator B (φ z * y)
  intro b
  calc
    b * (φ z * y) = 0 ↔ b * y ∈ I := by
      rw [← hann]
      change b * (φ z * y) = 0 ↔ b * y ∈ (Ideal.span ({φ z} : Set B)).annihilator
      rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      rw [show b * (φ z * y) = (b * y) * φ z by ring]
    _ ↔ Ideal.Quotient.mk I b * Ideal.Quotient.mk I y = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    _ ↔ Ideal.Quotient.mk I b ∈ maximalIdeal (B ⧸ I) := hy _
    _ ↔ b ∈ maximalIdeal B := by
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      change b ∈ (maximalIdeal (B ⧸ I)).comap (Ideal.Quotient.mk I) ↔ _
      rw [maximalIdeal_comap]

private theorem depth_eq_nat_of_flat_local (n : ℕ) :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
      (φ : A →+* B) [IsLocalHom φ] (_hflat : φ.Flat)
      [IsLocalRing (B ⧸ (maximalIdeal A).map φ)],
      depth (R := A) A + depth (R := B ⧸ (maximalIdeal A).map φ)
        (B ⧸ (maximalIdeal A).map φ) = (n : ℕ∞) → depth (R := B) B = (n : ℕ∞) := by
  induction n with
  | zero =>
    intro A B _ _ _ _ _ _ φ _ hflat _ hn
    obtain ⟨hA, hF⟩ := add_eq_zero.mp hn
    exact depth_zero_of_flat_local φ hflat hA hF
  | succ n ih =>
    intro A B _ _ _ _ _ _ φ _ hflat _ hn
    have hpos : 0 < depth (R := A) A +
        depth (R := B ⧸ (maximalIdeal A).map φ) (B ⧸ (maximalIdeal A).map φ) := by
      rw [hn]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨J, K, hJ, hK, hred⟩ := exists_depth_reducing_flat_local_quotients φ hflat hpos
    let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hJ)
    let : Nontrivial (B ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hK)
    let : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let : IsLocalRing (B ⧸ K) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
    obtain ⟨ψ, hψ, hflat', hF, _, hB, hsum⟩ := hred
    let := hψ
    let := hF
    have hsum' : depth (R := A ⧸ J) (A ⧸ J) +
        depth (R := (B ⧸ K) ⧸ (maximalIdeal (A ⧸ J)).map ψ)
          ((B ⧸ K) ⧸ (maximalIdeal (A ⧸ J)).map ψ) = (n : ℕ∞) := by
      apply ENat.add_left_injective_of_ne_top (show (1 : ℕ∞) ≠ ⊤ by simp)
      simpa only [Nat.cast_succ] using hsum.symm.trans hn
    rw [hB, ih ψ hflat' hsum']
    simp only [Nat.cast_succ]

/-- A flat local homomorphism of Noetherian local rings has a Noetherian local closed
fibre, with maximal ideal the image of the target's maximal ideal, and the depth of
its target is the sum of the depths of its source and closed fibre. -/
theorem depth_eq_add_of_flat_local {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat) :
    let I : Ideal S := (maximalIdeal R).map φ
    IsNoetherianRing (S ⧸ I) ∧
      ∃ hlocal : IsLocalRing (S ⧸ I),
        letI := hlocal
        (maximalIdeal S).map (Ideal.Quotient.mk I) = maximalIdeal (S ⧸ I) ∧
          depth (R := S) S = depth (R := R) R + depth (R := S ⧸ I) (S ⧸ I) := by
  let I : Ideal S := (maximalIdeal R).map φ
  let : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top φ).ne
  let : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  · obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top R)
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top (S ⧸ I))
    have hn : depth (R := R) R + depth (R := S ⧸ I) (S ⧸ I) = ((a + b : ℕ) : ℕ∞) := by
      rw [← ha, ← hb, Nat.cast_add]
    exact (depth_eq_nat_of_flat_local (a + b) φ hflat hn).trans hn.symm

end IsLocalRing
