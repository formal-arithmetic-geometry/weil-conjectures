/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.NoetherianSpace

import Mathlib.Algebra.Polynomial.CancelLeads

/-!
# Finite type algebras preserve Noetherian spectra

Source: J. Ohm and R. L. Pendleton, *Rings with Noetherian spectrum*,
Theorem 2.5 and Corollary 2.6 (the paper is not in the local collection).
The independent agent proof below uses least-degree polynomials and Noetherian induction,
serving paragraph (2) of `det-lem-coefficient-heart-closure` in main-20261015.
(blueprint: lem-sfb-finite-type-noetherian-spectrum)
-/

@[expose] public section

universe u v

open TopologicalSpace

namespace AlgebraicGeometry

open Polynomial _root_.PrimeSpectrum in
/-- A least-degree polynomial controls membership in primes away from its leading coefficient.
Cancel leading terms and induct on the degree of the other polynomial. -/
private theorem polynomial_ideal_generic_principal (R : Type u) [CommRing R]
    (I : Ideal R[X]) (hI : I ≠ ⊥) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ q : PrimeSpectrum R[X],
      C f.leadingCoeff ∉ q.asIdeal → (f ∈ q.asIdeal ↔ I ≤ q.asIdeal) := by
  classical
  obtain ⟨g, hg, hg0⟩ := (Submodule.ne_bot_iff _).mp hI
  have hex : ∃ n : ℕ, ∃ f ∈ I, f ≠ 0 ∧ f.natDegree = n :=
    ⟨g.natDegree, g, hg, hg0, rfl⟩
  obtain ⟨f, hf, hf0, hfn⟩ := Nat.find_spec hex
  have hmin (g : R[X]) (hg : g ∈ I) (hg0 : g ≠ 0) : f.natDegree ≤ g.natDegree := by
    rw [hfn]
    exact Nat.find_min' hex ⟨g, hg, hg0, rfl⟩
  refine ⟨f, hf, hf0, fun q ha ↦ ⟨?_, fun h ↦ h hf⟩⟩
  intro hfq g hg
  have main (n : ℕ) : ∀ g : R[X], g.natDegree = n → g ∈ I → g ∈ q.asIdeal := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hgn hg
      by_cases hg0 : g = 0
      · simp [hg0]
      have hfg := hmin g hg hg0
      by_cases hn : n = 0
      · have hfdeg : f.natDegree = 0 := by omega
        have hfc : f = C f.leadingCoeff := by
          simpa [leadingCoeff, hfdeg] using eq_C_of_natDegree_eq_zero hfdeg
        exact (ha (hfc ▸ hfq)).elim
      have hnpos : 0 < g.natDegree := by omega
      have hr : f.cancelLeads g ∈ I := by
        unfold cancelLeads
        exact I.sub_mem (I.mul_mem_left _ hg) (I.mul_mem_left _ hf)
      have hrd : (f.cancelLeads g).natDegree < n := by
        rw [← hgn]
        exact natDegree_cancelLeads_lt_of_natDegree_le_natDegree hfg hnpos
      have hrq := ih _ hrd (f.cancelLeads g) rfl hr
      have ht : C g.leadingCoeff * X ^ (g.natDegree - f.natDegree) * f ∈ q.asIdeal :=
        q.asIdeal.mul_mem_left _ hfq
      have hm : C f.leadingCoeff * g ∈ q.asIdeal := by
        have he : f.cancelLeads g = C f.leadingCoeff * g -
            C g.leadingCoeff * X ^ (g.natDegree - f.natDegree) * f := by
          simp [cancelLeads, Nat.sub_eq_zero_of_le hfg]
        rw [he] at hrq
        simpa only [sub_add_cancel] using q.asIdeal.add_mem hrq ht
      exact (q.isPrime.mem_or_mem hm).resolve_left ha
  exact main g.natDegree g rfl hg

open Polynomial _root_.PrimeSpectrum in
/-- If the complements of the nonzero coefficient basic opens are Noetherian, so is the spectrum.
For an open U, the least-degree polynomial for the ideal defining its complement identifies
U intersected with one such basic open with a compact basic open. -/
private theorem polynomial_noetherian_of_complements (R : Type u) [CommRing R]
    (hproper : ∀ a : R, a ≠ 0 →
      NoetherianSpace ↥((basicOpen (C a : R[X]) : Set (PrimeSpectrum R[X]))ᶜ)) :
    NoetherianSpace (PrimeSpectrum R[X]) := by
  classical
  apply (noetherianSpace_iff_opens _).mpr
  intro U
  let I := vanishingIdeal (U : Set (PrimeSpectrum R[X]))ᶜ
  have hzero : zeroLocus (I : Set R[X]) = (U : Set (PrimeSpectrum R[X]))ᶜ := by
    exact (zeroLocus_vanishingIdeal_eq_closure _).trans U.isOpen.isClosed_compl.closure_eq
  by_cases hI : I = ⊥
  · have hU : (U : Set (PrimeSpectrum R[X])) = ∅ := by
      apply compl_injective
      rw [← hzero, hI, zeroLocus_bot, Set.compl_empty]
    rw [hU]
    exact isCompact_empty
  obtain ⟨f, hf, hf0, hgen⟩ := polynomial_ideal_generic_principal R I hI
  let a := f.leadingCoeff
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  let D : Set (PrimeSpectrum R[X]) := basicOpen (C a)
  have heq : (U : Set (PrimeSpectrum R[X])) ∩ D =
      (basicOpen (C a * f) : Set (PrimeSpectrum R[X])) := by
    ext q
    have hmem : q ∈ (U : Set (PrimeSpectrum R[X])) ↔ ¬ I ≤ q.asIdeal := by
      have h := Set.ext_iff.mp hzero q
      simpa only [mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_compl_iff, not_not]
        using not_congr h.symm
    change (q ∈ (U : Set (PrimeSpectrum R[X])) ∧ C a ∉ q.asIdeal) ↔
      C a * f ∉ q.asIdeal
    rw [q.isPrime.mul_mem_iff_mem_or_mem, not_or]
    constructor
    · rintro ⟨hU, ha⟩
      exact ⟨ha, fun hfq ↦ (hmem.mp hU) ((hgen q ha).mp hfq)⟩
    · rintro ⟨ha, hfq⟩
      exact ⟨hmem.mpr (fun hi ↦ hfq (hi hf)), ha⟩
  have hc : IsCompact ((U : Set (PrimeSpectrum R[X])) ∩ D) := by
    rw [heq]
    exact isCompact_basicOpen _
  have hDc : NoetherianSpace ↥(Dᶜ) := hproper a ha
  have hc' : IsCompact ((U : Set (PrimeSpectrum R[X])) ∩ Dᶜ) :=
    (noetherianSpace_set_iff Dᶜ).mp hDc _ Set.inter_subset_right
  have hcover : (U : Set (PrimeSpectrum R[X])) =
      ((U : Set (PrimeSpectrum R[X])) ∩ D) ∪ ((U : Set (PrimeSpectrum R[X])) ∩ Dᶜ) := by
    exact (Set.inter_union_compl _ _).symm
  rw [hcover]
  exact hc.union hc'

open Polynomial _root_.PrimeSpectrum in
/-- The coefficientwise quotient identifies its spectrum with the inverse image of V(p). -/
private theorem polynomial_quotient_range (R : Type u) [CommRing R] (p : Ideal R) :
    Set.range (comap (mapRingHom (Ideal.Quotient.mk p))) =
      comap (C : R →+* R[X]) ⁻¹' zeroLocus (p : Set R) := by
  rw [range_comap_of_surjective _ _ (map_surjective _ Ideal.Quotient.mk_surjective),
    ker_mapRingHom, Ideal.mk_ker]
  ext q
  change p.map C ≤ q.asIdeal ↔ p ≤ q.asIdeal.comap C
  exact Ideal.map_le_iff_le_comap

open Polynomial _root_.PrimeSpectrum in
/-- Contraction to coefficients commutes with the coefficientwise quotient. -/
private theorem polynomial_quotient_square (R : Type u) [CommRing R] (p : Ideal R)
    (x : PrimeSpectrum (R ⧸ p)[X]) :
    comap C (comap (mapRingHom (Ideal.Quotient.mk p)) x) =
      comap (Ideal.Quotient.mk p) (comap C x) := by
  ext r
  change (mapRingHom (Ideal.Quotient.mk p)) (C r) ∈ x.asIdeal ↔
    C (Ideal.Quotient.mk p r) ∈ x.asIdeal
  rw [coe_mapRingHom, map_C]

/-- A union of two Noetherian subspaces is Noetherian, by compactness of all its subsets. -/
private theorem noetherian_union {X : Type*} [TopologicalSpace X] (s t : Set X)
    [NoetherianSpace s] [NoetherianSpace t] : NoetherianSpace (s ∪ t : Set X) := by
  apply (noetherianSpace_set_iff _).mpr
  intro v hv
  have heq : v = (v ∩ s) ∪ (v ∩ t) := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hv]
  rw [heq]
  exact ((noetherianSpace_set_iff s).mp inferInstance _ Set.inter_subset_right).union
    ((noetherianSpace_set_iff t).mp inferInstance _ Set.inter_subset_right)

open Polynomial _root_.PrimeSpectrum in
/-- Noetherian induction on closed subsets of the coefficient spectrum.
In the irreducible case quotient by its defining prime, then use the proper closed V(a)
for each nonzero coefficient a in the quotient domain. -/
private theorem polynomial_noetherian (R : Type u) [CommRing R]
    [NoetherianSpace (PrimeSpectrum R)] : NoetherianSpace (PrimeSpectrum R[X]) := by
  classical
  let π := comap (C : R →+* R[X])
  have main (Z : Closeds (PrimeSpectrum R)) : NoetherianSpace (π ⁻¹' (Z : Set _)) := by
    refine wellFounded_lt.induction (C := fun Z : Closeds (PrimeSpectrum R) ↦
      NoetherianSpace (π ⁻¹' (Z : Set (PrimeSpectrum R)))) Z ?_
    intro Z ih
    by_cases hZ : Z = ⊥
    · subst Z
      simp only [Closeds.coe_bot, Set.preimage_empty]
      infer_instance
    by_cases hirr : IsPreirreducible (Z : Set (PrimeSpectrum R))
    · have hZi : IsIrreducible (Z : Set (PrimeSpectrum R)) :=
        ⟨Closeds.coe_nonempty.mpr hZ, hirr⟩
      let p := vanishingIdeal (Z : Set (PrimeSpectrum R))
      have hp : p.IsPrime := isIrreducible_iff_vanishingIdeal_isPrime.mp hZi
      have hZeq : zeroLocus (p : Set R) = (Z : Set (PrimeSpectrum R)) :=
        (zeroLocus_vanishingIdeal_eq_closure _).trans Z.isClosed.closure_eq
      let j := comap (Ideal.Quotient.mk p)
      let k := comap (mapRingHom (Ideal.Quotient.mk p))
      have hj := isClosedEmbedding_comap_of_surjective (R ⧸ p)
        (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      have hk := isClosedEmbedding_comap_of_surjective (R ⧸ p)[X]
        (mapRingHom (Ideal.Quotient.mk p))
        (map_surjective _ Ideal.Quotient.mk_surjective)
      have hrangej : Set.range j = (Z : Set (PrimeSpectrum R)) := by
        rw [show j = comap (Ideal.Quotient.mk p) from rfl,
          range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hZeq]
      have hrangek : Set.range k = π ⁻¹' (Z : Set (PrimeSpectrum R)) := by
        rw [show k = comap (mapRingHom (Ideal.Quotient.mk p)) from rfl,
          polynomial_quotient_range, hZeq]
      have hquot : NoetherianSpace (PrimeSpectrum (R ⧸ p)[X]) := by
        apply polynomial_noetherian_of_complements
        intro a ha
        let W : Closeds (PrimeSpectrum R) :=
          ⟨j '' zeroLocus ({a} : Set (R ⧸ p)),
            hj.isClosedMap _ (isClosed_zeroLocus _)⟩
        have hWZ : W ≤ Z := by
          intro x hx
          change x ∈ (Z : Set (PrimeSpectrum R))
          rw [← hrangej]
          exact Set.image_subset_range j _ hx
        have hWne : W ≠ Z := by
          intro heq
          let x : PrimeSpectrum (R ⧸ p) := ⟨⊥, Ideal.isPrime_bot⟩
          have hxZ : j x ∈ (Z : Set (PrimeSpectrum R)) := hrangej ▸ ⟨x, rfl⟩
          have hxW : j x ∈ (W : Set (PrimeSpectrum R)) := heq ▸ hxZ
          obtain ⟨y, hy, hxy⟩ := hxW
          have hyx : y = x := hj.injective hxy
          subst y
          exact ha (by simpa [mem_zeroLocus, x] using hy)
        have hW := ih W (lt_of_le_of_ne hWZ hWne)
        let D : Set (PrimeSpectrum (R ⧸ p)[X]) :=
          (basicOpen (C a) : Set (PrimeSpectrum (R ⧸ p)[X]))ᶜ
        have hmap (x : D) : k x.val ∈ π ⁻¹' (W : Set (PrimeSpectrum R)) := by
          change π (k x.val) ∈ j '' zeroLocus ({a} : Set (R ⧸ p))
          refine ⟨comap C x.val, ?_, ?_⟩
          · rw [mem_zeroLocus, Set.singleton_subset_iff]
            have hx : ¬ C a ∉ x.val.asIdeal := x.property
            exact not_not.mp hx
          · exact (polynomial_quotient_square R p x.val).symm
        exact ((hk.isInducing.comp Topology.IsInducing.subtypeVal).codRestrict hmap).noetherianSpace
      let := hquot
      have hr := NoetherianSpace.range k hk.continuous
      rwa [hrangek] at hr
    · simp only [isPreirreducible_iff_isClosed_union_isClosed,
        not_forall, not_or] at hirr
      obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hz₁', hz₂'⟩ := hirr
      let Z₁ : Closeds (PrimeSpectrum R) := ⟨z₁, hz₁⟩
      let Z₂ : Closeds (PrimeSpectrum R) := ⟨z₂, hz₂⟩
      have hlt₁ : Z ⊓ Z₁ < Z := inf_lt_left.mpr (show ¬ Z ≤ Z₁ from hz₁')
      have h₁ := ih (Z ⊓ Z₁) hlt₁
      have hlt₂ : Z ⊓ Z₂ < Z := inf_lt_left.mpr (show ¬ Z ≤ Z₂ from hz₂')
      have h₂ := ih (Z ⊓ Z₂) hlt₂
      have heq : (Z : Set (PrimeSpectrum R)) =
          ((Z ⊓ Z₁ : Closeds _) : Set _) ∪ ((Z ⊓ Z₂ : Closeds _) : Set _) := by
        change (Z : Set _) = ((Z : Set _) ∩ z₁) ∪ ((Z : Set _) ∩ z₂)
        rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hcover]
      rw [heq, Set.preimage_union]
      let := h₁
      let := h₂
      exact noetherian_union _ _
  have h := main ⊤
  simpa only [Closeds.coe_top, Set.preimage_univ, noetherian_univ_iff] using h

/-- A finite type algebra over a ring with Noetherian spectrum has Noetherian spectrum.

Source: J. Ohm and R. L. Pendleton, *Rings with Noetherian spectrum*, Theorem 2.5 and
Corollary 2.6 (original paper unavailable locally). The following independent agent proof
serves paragraph (2) of `det-lem-coefficient-heart-closure`.

First prove the one-variable case by Noetherian induction on closed subsets Z of Spec R,
with claim that the inverse image under contraction Spec R[X] → Spec R is Noetherian.
The empty case is immediate; a reducible closed subset is a union of two smaller ones.
For irreducible Z, its vanishing ideal p is prime and Z = V(p). The coefficientwise
quotient R[X] → (R/p)[X] identifies its spectrum with the inverse image of Z.

For a nonzero ideal I in a polynomial ring choose a nonzero f in I of least natural degree,
with leading coefficient a. For any prime q avoiding C(a), membership f ∈ q implies I ⊆ q:
induct on the degree of g ∈ I and cancel the leading terms of f and g. The resulting
polynomial belongs to I and has smaller degree than g, so belongs to q by induction;
the other term is a multiple of f, hence C(a)g ∈ q, and primality gives g ∈ q.
When g has degree zero, so does f, and f = C(a) contradicts q avoiding C(a).

For an open U in Spec (R/p)[X], let I be the vanishing ideal of its closed complement.
If I = 0, U is empty. Otherwise the previous calculation gives U ∩ D(C(a)) = D(C(a)f),
which is compact. The image of V(a) in Spec R is a proper closed subset of Z, since
R/p is a domain and a ≠ 0. Induction says its inverse image is Noetherian; hence
U ∩ V(C(a)) is also compact. Their union is U, proving the one-variable assertion.

Induct on the finite number of variables, using the standard polynomial-ring equivalences.
A finite type algebra is a quotient of such a polynomial ring; the induced closed embedding
of spectra transfers Noetherianity. Empty spectra, zero rings and zero variables are included.
(blueprint: lem-sfb-finite-type-noetherian-spectrum) -/
theorem noetherianSpace_primeSpectrum_of_finiteType
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    (f : R →+* B) [NoetherianSpace (PrimeSpectrum R)]
    (hf : f.FiniteType) : NoetherianSpace (PrimeSpectrum B) := by
  let := f.toAlgebra
  have : Algebra.FiniteType R B := hf
  have hmv (n : ℕ) : NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin n) R)) := by
    induction n with
    | zero =>
      exact (noetherianSpace_iff_of_homeomorph
        (PrimeSpectrum.homeomorphOfRingEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)))).mpr
          inferInstance
    | succ n ih =>
      let := ih
      let := polynomial_noetherian (MvPolynomial (Fin n) R)
      exact (noetherianSpace_iff_of_homeomorph
        (PrimeSpectrum.homeomorphOfRingEquiv
          (MvPolynomial.finSuccEquiv R n).toRingEquiv)).mpr inferInstance
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let := hmv n
  have he := PrimeSpectrum.isClosedEmbedding_comap_of_surjective B g.toRingHom hg
  exact he.isInducing.noetherianSpace

end AlgebraicGeometry
