/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q132
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Localizing a compatible system of prime-power quotient isomorphisms

Source: Stacks Project, Algebra, Tag 00CT (`proposition-localize-quotient`),
and the explicit prime-extension and transition calculations in the DAG proof
(blueprint: lem-trf-adic-quotient-isomorphisms-localize).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace Localization

/-- A quotient isomorphism localizes at corresponding primes when the target ideal lies
in the target prime. Source: Stacks Project, Algebra, Tag 00CT
(`proposition-localize-quotient`). The quotient isomorphism identifies the images of the
prime complements: lift a target denominator modulo J and use J ≤ Q. Localize this
isomorphism, then identify its map with the canonical quotient map by extensionality.
(blueprint: lem-trf-adic-quotient-isomorphisms-localize)
-/
private theorem localized_quotient_bijective
    {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    (f : C →+* D) (p : Ideal C) (Q : Ideal D) [p.IsPrime] [Q.IsPrime]
    (hpQ : p = Q.comap f) (I : Ideal C) (J : Ideal D)
    (hJ : J ≤ Q) (hIJ : I ≤ J.comap f)
    (hb : Function.Bijective (Ideal.quotientMap J f hIJ))
    (hl : I.map (algebraMap C (Localization.AtPrime p)) ≤
      (J.map (algebraMap D (Localization.AtPrime Q))).comap
        (localRingHom p Q f hpQ)) :
    Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap D (Localization.AtPrime Q))) (localRingHom p Q f hpQ) hl) := by
  classical
  let e : (C ⧸ I) ≃+* (D ⧸ J) := RingEquiv.ofBijective _ hb
  have hM : (Algebra.algebraMapSubmonoid (C ⧸ I) p.primeCompl).map e.toMonoidHom =
      Algebra.algebraMapSubmonoid (D ⧸ J) Q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨f c, ?_, rfl⟩
      exact le_comap_primeCompl_iff.mpr (ge_of_eq hpQ) hc
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk J d)
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      change Ideal.Quotient.mk J (f c) = Ideal.Quotient.mk J d at hc
      have hcp : c ∈ p.primeCompl := by
        intro hcp
        have hfc : f c ∈ Q := by
          change c ∈ Q.comap f
          rwa [← hpQ]
        apply hd
        apply (Ideal.mem_quotient_iff_mem hJ).mp
        rw [← hc]
        exact (Ideal.mem_quotient_iff_mem hJ).mpr hfc
      exact ⟨Ideal.Quotient.mk I c, ⟨c, hcp, rfl⟩, hc⟩
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime p ⧸ I.map (algebraMap C (Localization.AtPrime p)))
    (Localization.AtPrime Q ⧸ J.map (algebraMap D (Localization.AtPrime Q))) e hM
  have he : E.toRingHom = Ideal.quotientMap
      (J.map (algebraMap D (Localization.AtPrime Q))) (localRingHom p Q f hpQ) hl := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext p.primeCompl
    ext c
    change E (algebraMap (C ⧸ I) _ (Ideal.Quotient.mk I c)) = _
    rw [IsLocalization.ringEquivOfRingEquiv_eq hM]
    simp only [e, RingEquiv.ofBijective_apply, Ideal.quotientMap_mk,
      RingHom.comp_apply, localRingHom_to_map]
    rfl
  rw [← he]
  exact E.bijective

/-- Global prime-power quotient isomorphisms give the canonical local quotient system.
Source: Stacks Project, Algebra, Tag 00CT (`proposition-localize-quotient`).
(blueprint: lem-trf-adic-quotient-isomorphisms-localize)

Proof:
1. The inclusion `p.map f ≤ Q` follows from contraction. Lift an element of `Q` using
   surjectivity at exponent one. Its lift lies in `p` by contraction, so `Q = p.map f`.
   This does not require `p` to be maximal.
2. Extension commutes with powers by `Ideal.map_pow`
   (`lemma-nagata-localization-ideal-pow`), both globally and in each localization.
3. Contraction sends denominators outside `p` to denominators outside `Q`, giving
   `localRingHom`. A fraction belongs to the extended prime precisely when its numerator
   belongs to the prime; thus the local map contracts the extended `Q` to the extended `p`.
   It induces maps on the quotients, with the displayed fraction formula.
4. Tag 00CT (`lem-weil-pbc-localization-at-prime-of-quotient`) identifies these quotients
   with localizations of the global quotients. A fraction `c/s` vanishes modulo the
   extended `p^n` exactly when `t*c ∈ p^n` for some `t ∉ p`, and similarly for `Q`.
5. For surjectivity lift the numerator and denominator modulo `Q^n` through the global
   quotient isomorphism; the lifted denominator stays outside `p`. For injectivity choose
   `v ∉ Q` killing `f(c)` modulo `Q^n`, lift `v` modulo `Q^n` to `f(t)`, and apply global
   injectivity to get `t*c ∈ p^n`, with `t ∉ p`. Step 4 then gives local injectivity.
6. If `n ≤ k`, powers decrease, so quotient transition maps exist. Both composites send
   `[c/s]` to `[f(c)/f(s)]` modulo exponent `n`. Every quotient element has such a fraction
   representative, proving compatibility.
-/
theorem adic_quotient_isomorphisms_localize
    {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    (f : C →+* D) (p : Ideal C) (Q : Ideal D) [p.IsPrime] [Q.IsPrime]
    (hpQ : p = Q.comap f)
    (hquot : ∀ n : ℕ, 1 ≤ n → Function.Bijective
      (Ideal.quotientMap ((p ^ n).map f) f (Ideal.le_comap_map :
        p ^ n ≤ ((p ^ n).map f).comap f))) :
    Q = p.map f ∧
    (∀ n : ℕ+, Q ^ (n : ℕ) = (p ^ (n : ℕ)).map f) ∧
    (Q.map (algebraMap D (Localization.AtPrime Q))).comap
        (Localization.localRingHom p Q f hpQ) =
      p.map (algebraMap C (Localization.AtPrime p)) ∧
    ∃ e : ∀ n : ℕ+,
        (Localization.AtPrime p ⧸
          (p.map (algebraMap C (Localization.AtPrime p))) ^ (n : ℕ)) ≃+*
        (Localization.AtPrime Q ⧸
          (Q.map (algebraMap D (Localization.AtPrime Q))) ^ (n : ℕ)),
      (∀ (n : ℕ+) (c : C) (s : p.primeCompl),
        e n (Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime p) c s)) =
          Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime Q) (f c)
            (⟨f s, le_comap_primeCompl_iff.mpr (ge_of_eq hpQ) s.2⟩ : Q.primeCompl))) ∧
      (∀ (k n : ℕ+) (hnk : n ≤ k)
        (x : Localization.AtPrime p ⧸
          (p.map (algebraMap C (Localization.AtPrime p))) ^ (k : ℕ)),
        e n (Ideal.Quotient.factor (Ideal.pow_le_pow_right hnk) x) =
          Ideal.Quotient.factor (Ideal.pow_le_pow_right hnk) (e k x)) := by
  classical
  have hmap : p.map f ≤ Q := Ideal.map_le_iff_le_comap.mpr hpQ.le
  have hsurj : Function.Surjective (Ideal.quotientMap (p.map f) f
      (Ideal.le_comap_map : p ≤ (p.map f).comap f)) := by
    have h := hquot 1 le_rfl
    rw [pow_one] at h
    exact h.2
  have hQ : Q = p.map f := by
    apply le_antisymm _ hmap
    intro d hd
    obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk (p.map f) d)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    change Ideal.Quotient.mk (p.map f) (f c) = Ideal.Quotient.mk (p.map f) d at hc
    have hfc : f c ∈ Q := by
      apply (Ideal.mem_quotient_iff_mem hmap).mp
      rw [hc]
      exact (Ideal.mem_quotient_iff_mem hmap).mpr hd
    have hcp : c ∈ p := by
      rw [hpQ]
      exact hfc
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hc]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hcp)
  have hpow (n : ℕ) : Q ^ n = (p ^ n).map f := by
    rw [hQ, Ideal.map_pow]
  let g := localRingHom p Q f hpQ
  let m := p.map (algebraMap C (Localization.AtPrime p))
  let q := Q.map (algebraMap D (Localization.AtPrime Q))
  have hlocal : q.comap g = m := by
    dsimp only [q, m, g]
    rw [AtPrime.map_eq_maximalIdeal, AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal_comap _
  have hle (n : ℕ) : m ^ n ≤ (q ^ n).comap g := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hlocal.ge) n
  let F (n : ℕ+) := Ideal.quotientMap (q ^ (n : ℕ)) g (hle n)
  have hb (n : ℕ+) : Function.Bijective (F n) := by
    have hn : 1 ≤ (n : ℕ) := n.pos
    have hqn : (p ^ (n : ℕ)).map f ≤ Q := by
      rw [← hpow]
      exact Ideal.pow_le_self n.ne_zero
    have hb' := localized_quotient_bijective f p Q hpQ
      (p ^ (n : ℕ)) ((p ^ (n : ℕ)).map f) hqn Ideal.le_comap_map (hquot n hn)
    rw [← hpow, Ideal.map_pow, Ideal.map_pow] at hb'
    exact hb' (hle n)
  refine ⟨hQ, fun n ↦ hpow n, hlocal, fun n ↦ RingEquiv.ofBijective (F n) (hb n), ?_, ?_⟩
  · intro n c s
    simp only [RingEquiv.ofBijective_apply, F, m, q, Ideal.quotientMap_mk, g,
      localRingHom_mk']
  · intro k n hnk x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end Localization
