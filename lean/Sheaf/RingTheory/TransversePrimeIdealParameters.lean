/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Transverse prime ideals and coordinate products in regular local rings

Source: Stacks Project, Etale Morphisms, Tag 0BIA, both local-ring arguments;
Algebra, Tags 00NR and 00NQ (blueprint: lem-sfb-transverse-prime-ideal-parameters).

## Main statements

* `RingTheory.exists_parameters_of_transverse_primes`: simultaneous principal generators.
* `RingTheory.parameter_product_ideal_properties`: coordinate products, primes, and strata.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- Transverse codimension-one regular prime quotients admit simultaneous parameters.
The supremum indexed by `Fin 0` is the zero ideal.

Source: Stacks Project, Tag 0BIA, converse local-ring argument, and Algebra Tags 00NR,
00NQ and Definition 00KU (blueprint: lem-sfb-transverse-prime-ideal-parameters).

Proof, steps 1 and 2 of the node: apply
`lem-weil-pbc-regular-local-quotient-kernel-parameters` to each proper prime ideal.
The quotient dimension formula of `lem-weil-pbc-regular-local-generators-regular-sequence`
shows that the initial parameter subfamily generating each ideal has length one.
Choose its generator. The total quotient dimension equality implies `r ≤ d`.
Choose `d - r` generators of the maximal ideal of the regular total quotient and lift
these into the maximal ideal of `R`. Every element of that maximal ideal is a linear
combination of these lifts modulo the sum of the prime ideals, and the difference is
a linear combination of their chosen generators. Thus the resulting `d` elements
generate the maximal ideal and form a regular system of parameters by
`def-weil-pbc-regular-system-of-parameters` and `def-weil-regular-scheme`.
For `r = 0`, simply choose a system of parameters of `R`. -/
theorem exists_parameters_of_transverse_primes
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (r : ℕ) (P : Fin r → Ideal R) (hDistinct : Function.Injective P)
    (hPrime : ∀ i : Fin r, (P i).IsPrime)
    (hRegular : ∀ i : Fin r, IsRegularLocalRing (R ⧸ P i))
    (hDimension : ∀ i : Fin r, ringKrullDim (R ⧸ P i) + 1 = (d : WithBot ℕ∞))
    (hTotalRegular : IsRegularLocalRing (R ⧸ (⨆ i : Fin r, P i)))
    (hTotalDimension : ringKrullDim R =
      ringKrullDim (R ⧸ (⨆ i : Fin r, P i)) + (r : WithBot ℕ∞)) :
    ∃ (hr : r ≤ d) (f : Fin d → R),
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn f) ∧
      ∀ i : Fin r, P i = Ideal.span {f (Fin.castLE hr i)} := by
  classical
  have _hDistinct := hDistinct
  have hprincipal (i : Fin r) : ∃ x : R, P i = Ideal.span {x} := by
    have := hRegular i
    obtain ⟨xs, c, hc, hxs, hI⟩ :=
      exists_parameters_regularLocalQuotient R d hd (P i) (hPrime i).ne_top
    have hq := (IsRegularLocalRing.isRegular_and_quotients_of_generators
      R d hd xs hxs).2.1 c hc
    have hdim := hDimension i
    rw [hI, hq.2] at hdim
    have hnat : d - c + 1 = d := by exact_mod_cast hdim
    have hc1 : c = 1 := by omega
    have hlen : xs.length = d := by exact_mod_cast hxs.2.trans hd
    have htlen : (xs.take c).length = 1 := by simp [hc1, hlen, show 1 ≤ d by omega]
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp htlen
    exact ⟨x, by simpa [hx] using hI⟩
  choose g hg using hprincipal
  let I := ⨆ i : Fin r, P i
  have hI : I ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    exact iSup_le fun i ↦ IsLocalRing.le_maximalIdeal (hPrime i).ne_top
  have := hTotalRegular
  obtain ⟨xs, c, hc, hxs, hkernel⟩ :=
    exists_parameters_regularLocalQuotient R d hd I hI
  have hq := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R d hd xs hxs).2.1 c hc
  have hdim : (d : WithBot ℕ∞) = ((d - c : ℕ) : WithBot ℕ∞) + r := by
    rw [← hd, ← hq.2, ← hkernel]
    exact hTotalDimension
  have hnat : d = d - c + r := by exact_mod_cast hdim
  have hcr : c = r := by omega
  have hr : r ≤ d := by omega
  have hlen : xs.length = d := by exact_mod_cast hxs.2.trans hd
  have hgspan : Ideal.ofList (List.ofFn g) = I := by
    have he : {x | x ∈ List.ofFn g} = Set.range g := by ext x; simp
    rw [Ideal.ofList, he, Ideal.span_range_eq_iSup]
    exact iSup_congr fun i ↦ (hg i).symm
  let ys := List.ofFn g ++ xs.drop r
  have hylen : ys.length = d := by simp [ys, hlen]; omega
  have hyreg : IsLocalRing.IsRegularSystemOfParameters ys := by
    constructor
    · change Ideal.ofList ys = _
      dsimp [ys]
      rw [Ideal.ofList_append, hgspan, hkernel, hcr,
        ← Ideal.ofList_append, List.take_append_drop]
      exact hxs.1
    · rw [hylen, hd]
  let f : Fin d → R := fun j ↦ ys[j.val]'(by omega)
  have hflist : List.ofFn f = ys := by
    apply List.ext_getElem
    · simp [hylen]
    · intro i hi hj
      simp [f]
  refine ⟨hr, f, hflist.symm ▸ hyreg, ?_⟩
  intro i
  rw [hg i]
  congr 1
  simp [f, ys, List.getElem_append_left, i.isLt]


private theorem parameter_subset_quotient
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (t : Fin d → R) (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (s : Finset (Fin d)) :
    IsRegularLocalRing (R ⧸ Ideal.span (t '' (s : Set (Fin d)))) ∧
      ringKrullDim (R ⧸ Ideal.span (t '' (s : Set (Fin d)))) =
        ((d - s.card : ℕ) : WithBot ℕ∞) := by
  classical
  let xs := s.toList.map t ++ (Finset.univ \ s).toList.map t
  have hs : s.card ≤ d := by simpa using Finset.card_le_card (Finset.subset_univ s)
  have hlen : xs.length = d := by
    simp only [xs, List.length_append, List.length_map, Finset.length_toList,
      Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, Fintype.card_fin]
    omega
  have hset : {x | x ∈ xs} = {x | x ∈ List.ofFn t} := by
    ext x
    simp only [xs, List.mem_append, List.mem_map, Finset.mem_toList,
      Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩) <;> exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      by_cases his : i ∈ s
      · exact Or.inl ⟨i, his, hi⟩
      · exact Or.inr ⟨i, his, hi⟩
  have hxs : IsLocalRing.IsRegularSystemOfParameters xs :=
    ⟨hset.symm ▸ ht.1, by rw [hlen, hd]⟩
  have htake : xs.take s.card = s.toList.map t := by
    have hl : (s.toList.map t).length = s.card := by simp
    change (s.toList.map t ++ _).take s.card = _
    rw [← hl, List.take_left]
  have hideal : Ideal.ofList (xs.take s.card) = Ideal.span (t '' (s : Set (Fin d))) := by
    rw [htake, Ideal.ofList]
    congr 1
    ext x
    simp
  have hq := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    R d hd xs hxs).2.1 s.card hs
  rwa [hideal] at hq

/-- A product of distinct coordinates cuts out a reduced Cartier divisor, with precisely
those coordinate primes as its minimal primes; all coordinate strata are regular.

Source: Stacks Project, Tag 0BIA, forward local-ring argument, and Algebra Tags 00NQ,
00NP and 00LF (blueprint: lem-sfb-transverse-prime-ideal-parameters).

Proof, steps 3 through 6 of the node: permute parameters to put any selected coordinate
first, and apply `lem-weil-pbc-regular-local-generators-regular-sequence`. Its quotient
is regular local, hence a domain by `lem-sc-regular-local-domain`; its ideal is prime.
Put two distinct coordinates first: the second is a nonzerodivisor on the nonzero
first quotient, so it does not belong to the first ideal. This proves incomparability.
Regular sequences (`def-weil-pbc-regular-sequence`) also show that each coordinate
is a nonzerodivisor; so is their product, by composing injective multiplication maps.
Induct on the number of factors to identify the product ideal with their intersection:
write an element in the intersection as the previous product times a coefficient;
primality of the final ideal and incomparability force this coefficient into that ideal.
The reverse inclusion follows from divisibility. An intersection of primes is radical.
Any prime containing the product contains a factor, so minimality and incomparability
identify its minimal primes with exactly the coordinate ideals. For an arbitrary
subset, permute its coordinates first and apply the same parameter-quotient theorem
with its cardinality. The empty product is one, its ideal and the empty intersection
are the whole ring, and no proper prime can contain this ideal. The empty stratum is
`R`; selecting all `d` coordinates gives the residue field. -/
theorem parameter_product_ideal_properties
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (t : Fin d → R) (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (r : ℕ) (hr : r ≤ d) :
    (∏ i : Fin r, t (Fin.castLE hr i)) ∈ nonZeroDivisors R ∧
    (∀ i : Fin r, (Ideal.span {t (Fin.castLE hr i)}).IsPrime) ∧
    (Pairwise fun i j : Fin r ↦
      ¬ Ideal.span {t (Fin.castLE hr i)} ≤ Ideal.span {t (Fin.castLE hr j)}) ∧
    Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)} =
      ⨅ i : Fin r, Ideal.span {t (Fin.castLE hr i)} ∧
    (Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)}).IsRadical ∧
    (∀ p : Ideal R,
      p ∈ (Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)}).minimalPrimes ↔
        ∃ i : Fin r, p = Ideal.span {t (Fin.castLE hr i)}) ∧
    (∀ J : Finset (Fin r),
      IsRegularLocalRing
        (R ⧸ Ideal.span ((fun i : Fin r ↦ t (Fin.castLE hr i)) '' (J : Set (Fin r)))) ∧
      ringKrullDim
        (R ⧸ Ideal.span ((fun i : Fin r ↦ t (Fin.castLE hr i)) '' (J : Set (Fin r)))) =
          ((d - J.card : ℕ) : WithBot ℕ∞)) ∧
    (r = 0 → Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)} = ⊤ ∧
      ∀ p : Ideal R, p.IsPrime →
        ¬ Ideal.span {∏ i : Fin r, t (Fin.castLE hr i)} ≤ p) := by
  classical
  have hsingle (i : Fin d) :
      IsRegularLocalRing (R ⧸ Ideal.span {t i}) ∧
        ringKrullDim (R ⧸ Ideal.span {t i}) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    have h := parameter_subset_quotient R d hd t ht {i}
    have he : t '' (({i} : Finset (Fin d)) : Set (Fin d)) = {t i} := by
      ext x
      simp
    rw [he] at h
    simpa only [Finset.card_singleton] using h
  have hprime (i : Fin d) : (Ideal.span {t i}).IsPrime := by
    have := (hsingle i).1
    exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hnezero (i : Fin d) : t i ≠ 0 := by
    intro hz
    have hq := (hsingle i).2
    rw [hz, Ideal.span_singleton_zero, (RingEquiv.quotientBot R).ringKrullDim, hd] at hq
    have he : d = d - 1 := by exact_mod_cast hq
    have := i.isLt
    omega
  have hincomp : Pairwise fun i j : Fin d ↦
      ¬ Ideal.span {t i} ≤ Ideal.span {t j} := by
    intro i j hij hle
    have hcard : ({i, j} : Finset (Fin d)).card = 2 := by simp [hij]
    have hideal : Ideal.span (t '' ({i, j} : Finset (Fin d))) = Ideal.span {t j} := by
      simp [Set.image_insert_eq, Ideal.span_insert, sup_eq_right.mpr hle]
    have hq := (parameter_subset_quotient R d hd t ht {i, j}).2
    rw [hideal, hcard, (hsingle j).2] at hq
    have he : d - 1 = d - 2 := by exact_mod_cast hq
    have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    have := i.isLt
    have := j.isLt
    omega
  let v : Fin r → R := fun i ↦ t (Fin.castLE hr i)
  let A : Fin r → Ideal R := fun i ↦ Ideal.span {v i}
  have hA (i : Fin r) : (A i).IsPrime := hprime (Fin.castLE hr i)
  have hinc : Pairwise fun i j : Fin r ↦ ¬ A i ≤ A j := by
    intro i j hij
    exact hincomp (fun h ↦ hij (Fin.castLE_injective hr h))
  have hdiv (s : Finset (Fin r)) (x : R) :
      (∀ i ∈ s, x ∈ A i) → (∏ i ∈ s, v i) ∣ x := by
    induction s using Finset.induction_on generalizing x with
    | empty => simp
    | @insert a s ha ih =>
      intro hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hx a (by simp))
      rw [Finset.prod_insert ha, hb]
      apply mul_dvd_mul_left
      apply ih
      intro i hi
      have hmem : v a * b ∈ A i := hb ▸ hx i (by simp [hi])
      have hnot : v a ∉ A i := by
        intro h
        have hai : a ≠ i := by intro he; exact ha (he.symm ▸ hi)
        exact hinc hai ((Ideal.span_singleton_le_iff_mem _).mpr h)
      exact ((hA i).mem_or_mem hmem).resolve_left hnot
  have heq : Ideal.span {∏ i : Fin r, v i} = ⨅ i : Fin r, A i := by
    apply le_antisymm
    · apply le_iInf
      intro i
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem v (Finset.mem_univ i))
    · intro x hx
      apply Ideal.mem_span_singleton.mpr
      exact hdiv Finset.univ x (fun i _ ↦ (Ideal.mem_iInf.mp hx) i)
  have hcover (p : Ideal R) (hp : p.IsPrime)
      (hle : Ideal.span {∏ i : Fin r, v i} ≤ p) : ∃ i : Fin r, A i ≤ p := by
    rw [← Ideal.prod_span_singleton] at hle
    obtain ⟨i, -, hi⟩ := hp.prod_le.mp hle
    exact ⟨i, hi⟩
  have hminimal (p : Ideal R) :
      p ∈ (Ideal.span {∏ i : Fin r, v i}).minimalPrimes ↔
        ∃ i : Fin r, p = A i := by
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := hcover p hp.isPrime hp.le
      refine ⟨i, le_antisymm ?_ hi⟩
      exact hp.2 ⟨hA i, heq.symm ▸ iInf_le A i⟩ hi
    · rintro ⟨i, rfl⟩
      refine ⟨⟨hA i, heq.symm ▸ iInf_le A i⟩, ?_⟩
      intro p hp hpi
      obtain ⟨j, hj⟩ := hcover p hp.1 hp.2
      have hji : j = i := by
        by_contra hne
        exact hinc hne (hj.trans hpi)
      exact hji ▸ hj
  refine ⟨?_, hA, hinc, heq, ?_, hminimal, ?_, ?_⟩
  · apply prod_mem_nonZeroDivisors_of_mem_nonZeroDivisors
    intro i _
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (hnezero (Fin.castLE hr i))
  · rw [heq]
    exact Ideal.isRadical_iInf A (fun i ↦ (hA i).isRadical)
  · intro J
    let s := J.image (Fin.castLE hr)
    have hcard : s.card = J.card := Finset.card_image_of_injective _
      (Fin.castLE_injective hr)
    have himage : t '' (s : Set (Fin d)) = v '' (J : Set (Fin r)) := by
      simp [s, v, Finset.coe_image, Set.image_image]
    have hq := parameter_subset_quotient R d hd t ht s
    rwa [himage, hcard] at hq
  · intro hzero
    have hone : Ideal.span {∏ i : Fin r, v i} = ⊤ := by
      subst r
      simp
    refine ⟨hone, ?_⟩
    intro p hp hle
    exact hp.ne_top (top_le_iff.mp (hone ▸ hle))

end RingTheory
