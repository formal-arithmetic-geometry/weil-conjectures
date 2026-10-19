/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N5 and F9
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# A regular sequence at a prime spreads to a principal neighbourhood

Source: literature/stacks-project/algebra.tex, Tag 061L, lemma-regular-sequence-in-neighbourhood
(specializing the finite module to the ring; blueprint:
lem-exc-regular-sequence-principal-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- The colon ideal `(I : x)` is finitely generated. Clearing denominators on its
finite generators yields one multiplier outside `p` sending it into `I`. -/
private lemma exists_mul_mem_of_regular_atPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p I : Ideal R) [p.IsPrime] (x : R)
    (h : IsSMulRegular
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      (algebraMap R (Localization.AtPrime p) x)) :
    ∃ g ∉ p, ∀ a : R, x * a ∈ I → g * a ∈ I := by
  classical
  let K : Ideal R := Submodule.comap (LinearMap.lsmul R R x) I
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian K : K.FG)
  have hgen (a : R) (ha : a ∈ T) : ∃ s ∉ p, s * a ∈ I := by
    have haK : a ∈ K := hT ▸ Ideal.subset_span ha
    have hxa : x * a ∈ I := haK
    have ha' : algebraMap R (Localization.AtPrime p) a ∈
        I.map (algebraMap R (Localization.AtPrime p)) := by
      apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp h
      simpa only [smul_eq_mul, ← map_mul] using Ideal.mem_map_of_mem _ hxa
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
      p.primeCompl (Localization.AtPrime p) I a).mp ha'
  choose! s hs hsI using hgen
  refine ⟨∏ a ∈ T, s a, p.primeCompl.prod_mem (fun a ha ↦ hs a ha), ?_⟩
  have hle : K ≤ Submodule.comap (LinearMap.lsmul R R (∏ a ∈ T, s a)) I := by
    rw [← hT]
    apply Submodule.span_le.mpr
    intro b hb
    change (∏ a ∈ T, s a) * b ∈ I
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s hb
    rw [hc, mul_comm (s b), mul_assoc]
    exact I.mul_mem_left c (hsI b hb)
  exact fun a ha ↦ hle ha

/-- A multiplier sending `(I : x)` into `I` makes `x` regular on the localized
quotient after that multiplier is inverted; clear the denominator of an element. -/
private lemma regular_away_of_mul_mem
    {R : Type u} [CommRing R] (I : Ideal R) (x g : R)
    (h : ∀ a : R, x * a ∈ I → g * a ∈ I) :
    IsSMulRegular
      (Localization.Away g ⧸ I.map (algebraMap R (Localization.Away g)))
      (algebraMap R (Localization.Away g) x) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro z hz
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers g) z
  have hz' : IsLocalization.mk' (Localization.Away g) (x * a) t ∈
      I.map (algebraMap R (Localization.Away g)) := by
    simpa only [smul_eq_mul, IsLocalization.mul_mk'_eq_mk'_of_mul] using hz
  obtain ⟨s, hs, hsa⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff
    (Submonoid.powers g) (Localization.Away g) I (x * a) t).mp hz'
  apply (IsLocalization.mk'_mem_map_algebraMap_iff
    (Submonoid.powers g) (Localization.Away g) I a t).mpr
  refine ⟨g * s, (Submonoid.powers g).mul_mem (Submonoid.mem_powers g) hs, ?_⟩
  simpa only [mul_assoc] using h (s * a) (by simpa only [mul_left_comm x s] using hsa)

/--
Source: Stacks Project, algebra.tex, Tag 061L, lemma-regular-sequence-in-neighbourhood,
specializing the finite module to the ring.
(blueprint: lem-exc-regular-sequence-principal-neighbourhood)

Proof (the finite-kernel argument of Tag 061L, using inverse images in `R`):

1. For a prefix ideal `I` and next element `x`, the kernel on `R/I` has inverse
   image `K = {a | x*a ∈ I}`. Noetherianity makes this ideal finitely generated.
2. For a generator `a` of `K`, regularity on the localized quotient implies
   `a/1 ∈ I R_p`. The fraction membership criterion gives `s ∉ p` with `s*a ∈ I`.
3. Multiply these denominators. Each divides their product `g`, so `g*a ∈ I`
   on the generators, hence on their span `K`. Multiply the resulting `g` for
   all prefixes to obtain a common `G ∉ p`. Empty products are `1`.
4. If `(x/1)*(a/t) ∈ I R[1/G]`, the membership criterion gives a power `s` of
   `G` with `s*x*a ∈ I`. Step 3 gives `G*s*a ∈ I`. Since `G*s` is a denominator,
   the same membership criterion gives `a/t ∈ I R[1/G]`. This proves weak
   regularity, using `Ideal.map_ofList` for the prefix ideals.
5. The final ideal `I_r R_p` is proper by the assumed regularity. The ideal
   localization criterion identifies this with disjointness of `I_r` from the
   complement of `p`, so `I_r ≤ p`.
6. No power of `G` belongs to `I_r`, since primality would force `G ∈ p`.
   Thus `I_r R[1/G]` is proper by the same criterion. This proves the nonzero
   final quotient clause, also for the empty list with `I_r = 0` and `G = 1`.

The private helpers implement steps 1--3 and step 4. This version needs no
explicit module-localization or localization-exactness comparison.
-/
theorem exists_isRegular_localizationAway_of_isRegular_localizationAtPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]
    (r : ℕ) (x : Fin r → R)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (List.ofFn (fun i ↦ algebraMap R (Localization.AtPrime p) (x i)))) :
    ∃ g : R, g ∉ p ∧
      RingTheory.Sequence.IsRegular (Localization.Away g)
        (List.ofFn (fun i ↦ algebraMap R (Localization.Away g) (x i))) := by
  classical
  let rs := List.ofFn x
  have hreg' : Sequence.IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p))) := by
    simpa only [rs, List.map_ofFn, Function.comp_def] using hreg
  have hIp : Ideal.ofList rs ≤ p := by
    have hproper : (Ideal.ofList rs).map (algebraMap R (Localization.AtPrime p)) ≠ ⊤ := by
      simpa only [Ideal.map_ofList, Ideal.smul_eq_mul, Ideal.mul_top] using
        hreg'.top_ne_smul.symm
    have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint p.primeCompl
      (Localization.AtPrime p) (Ideal.ofList rs)).mp hproper
    intro a ha
    by_contra hap
    exact Set.disjoint_left.mp hd hap ha
  have hi (i : Fin rs.length) :
      IsSMulRegular (Localization.AtPrime p ⧸
        (Ideal.ofList (rs.take i)).map (algebraMap R (Localization.AtPrime p)))
        (algebraMap R (Localization.AtPrime p) rs[i]) := by
    have h := hreg'.regular_mod_prev i (by simpa only [List.length_map] using i.isLt)
    simp only [List.getElem_map] at h
    rw [← List.map_take, ← Ideal.map_ofList, Ideal.smul_eq_mul, Ideal.mul_top] at h
    exact h
  choose g hg hkill using fun i : Fin rs.length ↦
    exists_mul_mem_of_regular_atPrime p (Ideal.ofList (rs.take i)) rs[i] (hi i)
  let G := ∏ i, g i
  have hG : G ∉ p := p.primeCompl.prod_mem (fun i _ ↦ hg i)
  have hweak : Sequence.IsWeaklyRegular (Localization.Away G)
      (rs.map (algebraMap R (Localization.Away G))) := by
    constructor
    intro i hi
    have hi' : i < rs.length := by simpa only [List.length_map] using hi
    have h := regular_away_of_mul_mem (Ideal.ofList (rs.take i)) rs[i] G (by
      intro a ha
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g (Finset.mem_univ (⟨i, hi'⟩ : Fin rs.length))
      change (∏ j, g j) * a ∈ Ideal.ofList (rs.take i)
      rw [hc, mul_comm (g ⟨i, hi'⟩), mul_assoc]
      exact (Ideal.ofList (rs.take i)).mul_mem_left c (hkill ⟨i, hi'⟩ a ha))
    simp only [List.getElem_map]
    rw [← List.map_take, ← Ideal.map_ofList, Ideal.smul_eq_mul, Ideal.mul_top]
    exact h
  have hproper : (Ideal.ofList rs).map (algebraMap R (Localization.Away G)) ≠ ⊤ := by
    apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers G)
      (Localization.Away G) (Ideal.ofList rs)).mpr
    apply Set.disjoint_left.mpr
    intro a ha haI
    obtain ⟨n, rfl⟩ := ha
    exact hG (Ideal.IsPrime.mem_of_pow_mem (inferInstance : p.IsPrime) n (hIp haI))
  refine ⟨G, hG, ?_⟩
  have hregular : Sequence.IsRegular (Localization.Away G)
      (rs.map (algebraMap R (Localization.Away G))) := by
    refine ⟨hweak, ?_⟩
    simpa only [← Ideal.map_ofList, Ideal.smul_eq_mul, Ideal.mul_top] using hproper.symm
  simpa only [rs, List.map_ofFn, Function.comp_def] using hregular

end RingTheory
