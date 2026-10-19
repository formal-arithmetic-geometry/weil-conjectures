/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.Irreducible

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Irreducibility of an affine linear incidence hypersurface

Source: Stacks Project, `more-morphisms.tex`, Tag 0G4F, lemma `lemma-bertini-irreducible`,
middle proof paragraph (blueprint: lem-zl-linear-incidence-irreducible).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

open MvPolynomial

private theorem linear_prime_of_unit {R ι : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] (f : ι → R) (j : ι) (hj : IsUnit (f j)) :
    Prime (∑ i, C (f i) * X i : MvPolynomial ι R) := by
  classical
  obtain ⟨u, hu⟩ := hj
  let t : MvPolynomial ι R := ∑ i ∈ Finset.univ.erase j, C (f i) * X i
  let g : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    aeval (fun i ↦ if i = j then C (f j) * X j + t else X i)
  let h : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    aeval (fun i ↦ if i = j then C (↑(u⁻¹) : R) * (X j - t) else X i)
  have gt : g t = t := by
    simp only [t, map_sum, map_mul, aeval_C, g]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  have ht : h t = t := by
    simp only [t, map_sum, map_mul, aeval_C, h]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  have gh : g.comp h = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change g (h (X i)) = X i
    by_cases hi : i = j
    · subst i
      rw [show h (X j) = C (↑(u⁻¹) : R) * (X j - t) by simp [h]]
      rw [map_mul, map_sub, gt]
      simp only [g, aeval_C, aeval_X, MvPolynomial.algebraMap_eq, ↓reduceIte]
      rw [add_sub_cancel_right, ← mul_assoc, ← map_mul, ← hu,
        Units.inv_mul, map_one, one_mul]
    · simp [g, h, hi]
  have hg : h.comp g = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change h (g (X i)) = X i
    by_cases hi : i = j
    · subst i
      rw [show g (X j) = C (f j) * X j + t by simp [g]]
      rw [map_add, map_mul, ht]
      simp only [h, aeval_C, aeval_X, MvPolynomial.algebraMap_eq, ↓reduceIte]
      rw [← hu, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
      ring
    · simp [g, h, hi]
  let e := AlgEquiv.ofAlgHom g h gh hg
  have he : e (X j) = ∑ i, C (f i) * X i := by
    change g (X j) = _
    simp only [g, aeval_X, ↓reduceIte]
    exact Finset.add_sum_erase _ _ (Finset.mem_univ j)
  rw [← he]
  exact (MulEquiv.prime_iff e).mpr (MvPolynomial.X_prime (i := j))

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem minimal_eq_localized_linear {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsDomain S] [Fintype ι]
    (M : Submonoid R) [IsLocalization M S] (f : ι → R) (j : ι)
    (hj : IsUnit (algebraMap R S (f j))) (Q : Ideal (MvPolynomial ι R))
    (hQ : Q ∈ (Ideal.span {∑ i, C (f i) * X i}).minimalPrimes)
    (hd : Disjoint (M.map (C (σ := ι)) : Set (MvPolynomial ι R)) Q) :
    Q = (Ideal.span {∑ i, C (algebraMap R S (f i)) * X i}).comap
      (MvPolynomial.map (algebraMap R S)) := by
  have : Q.IsPrime := hQ.isPrime
  let I : Ideal (MvPolynomial ι R) := Ideal.span {∑ i, C (f i) * X i}
  let g := algebraMap (MvPolynomial ι R) (MvPolynomial ι S)
  have he : I.map g = Ideal.span {∑ i, C (algebraMap R S (f i)) * X i} := by
    simp [I, g, Ideal.map_span]
  have hp : (I.map g).IsPrime := by
    have hl := linear_prime_of_unit (fun i ↦ algebraMap R S (f i)) j hj
    rw [he]
    exact (Ideal.span_singleton_prime hl.ne_zero).mpr hl
  have hle : (I.map g).comap g ≤ Q := by
    calc
      (I.map g).comap g ≤ (Q.map g).comap g :=
        Ideal.comap_mono (Ideal.map_mono hQ.le)
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint
        (M.map (C (σ := ι))) (MvPolynomial ι S) hQ.isPrime hd
  have heq : Q = (I.map g).comap g :=
    le_antisymm (hQ.2 ⟨hp.comap g, Ideal.le_comap_map⟩ hle) hle
  rw [he] at heq
  exact heq

private theorem constant_eq_zero_of_mem_linear {R S ι : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Fintype ι]
    (hinj : Function.Injective (algebraMap R S)) (f : ι → S) (a : R)
    (ha : MvPolynomial.map (algebraMap R S) (C a : MvPolynomial ι R) ∈
      Ideal.span {∑ i, C (f i) * X i}) : a = 0 := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hh := congrArg (constantCoeff : MvPolynomial ι S →+* S) hb
  apply hinj
  simpa using hh

private theorem minimal_linear_avoids_coefficient {R ι : Type*} [CommRing R]
    [IsNoetherianRing R] [Fintype ι] (f : ι → R)
    (hJ : ∀ p : Ideal R, p ∈ (Ideal.span (Set.range f)).minimalPrimes →
      (2 : ℕ∞) ≤ p.height)
    (Q : Ideal (MvPolynomial ι R))
    (hQ : Q ∈ (Ideal.span {∑ i, C (f i) * X i}).minimalPrimes) :
    ∃ j, C (f j) ∉ Q := by
  classical
  have : Q.IsPrime := hQ.isPrime
  have hheight : Q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hQ
  by_contra! h
  let p := Q.under R
  have : p.IsPrime := inferInstance
  have hle : Ideal.span (Set.range f) ≤ p := by
    rw [Ideal.span_le, Set.range_subset_iff]
    exact h
  obtain ⟨p₀, hp₀, h₀⟩ := Ideal.exists_minimalPrimes_le hle
  have ht : (2 : ℕ∞) ≤ p.height := (hJ p₀ hp₀).trans (Ideal.height_mono h₀)
  have he := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q
  have hlt : p.height ≤ Q.height := by
    rw [he]
    exact le_self_add
  have : (2 : ℕ∞) ≤ 1 := ht.trans (hlt.trans hheight)
  norm_num at this

private theorem minimal_linear_contracts_zero {R ι : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Fintype ι]
    (f : ι → R)
    (hJ : ∀ p : Ideal R, p ∈ (Ideal.span (Set.range f)).minimalPrimes →
      (2 : ℕ∞) ≤ p.height)
    (Q : Ideal (MvPolynomial ι R))
    (hQ : Q ∈ (Ideal.span {∑ i, C (f i) * X i}).minimalPrimes) :
    ∀ a : R, C a ∈ Q → a = 0 := by
  classical
  have : Q.IsPrime := hQ.isPrime
  obtain ⟨j, hj⟩ := minimal_linear_avoids_coefficient f hJ Q hQ
  have hj₀ : f j ≠ 0 := fun h ↦ hj (by simp [h])
  let S := Localization.Away (f j)
  have : IsDomain S := Localization.Away.isDomain hj₀
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hj₀)
  have hd : Disjoint ((Submonoid.powers (f j)).map (C (σ := ι)) :
      Set (MvPolynomial ι R)) Q := by
    rw [Submonoid.map_powers]
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hj
  have hjunit : IsUnit (algebraMap R S (f j)) :=
    IsLocalization.map_units S ⟨f j, Submonoid.mem_powers _⟩
  have he := minimal_eq_localized_linear (S := S) (Submonoid.powers (f j))
    f j hjunit Q hQ hd
  intro a ha
  rw [he] at ha
  exact constant_eq_zero_of_mem_linear hinj _ a ha

/--
Let `A` be a finite type domain over a field `k`.  If the coefficients of a nonzero
linear form in at least one variable have a common vanishing locus of height at least
two, then the spectrum of its quotient polynomial ring is irreducible.  The statement
asserts irreducibility only; it makes no reducedness claim.

Source: Stacks Project, `more-morphisms.tex`, Tag 0G4F, lemma `lemma-bertini-irreducible`,
middle proof paragraph (blueprint: lem-zl-linear-incidence-irreducible).
Proof: Put `B = A[x_i]` and `L = ∑ f_i x_i`; `B` is a Noetherian domain and `L` is nonzero.
On each coefficient open, substitution identifies the kernel of evaluation at the solved
variable and clearing denominators shows that every minimal prime over `(L)` contains
that kernel.  The height bound for a principal quotient gives height at most one for
such a minimal prime.  If all coefficients lay in it, extending a length-two prime chain
under a minimal prime over their ideal would contradict that bound.  Hence a coefficient
is outside, forcing the minimal prime to be the substitution kernel; all minimal primes
therefore coincide.  The quotient spectrum is the corresponding irreducible closed set.
The argument uses the finite-type, polynomial-ring, localization, height, minimal-prime,
and irreducible-spectrum facts listed in the DAG proof dependencies.
-/
theorem linear_incidence_irreducible
    (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A) (hf : ∃ i, f i ≠ 0)
    (hJ : ∀ p : Ideal A, p ∈ (Ideal.span (Set.range f)).minimalPrimes →
      (2 : ℕ∞) ≤ p.height) :
    IrreducibleSpace
      (Spec (CommRingCat.of
        (MvPolynomial (Fin r) A ⧸ Ideal.span
          {∑ i : Fin r, MvPolynomial.C (f i) * MvPolynomial.X i}))) := by
  classical
  have _ := hr
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let K := FractionRing A
  let I : Ideal (MvPolynomial (Fin r) A) := Ideal.span {∑ i, C (f i) * X i}
  let g := MvPolynomial.map (σ := Fin r) (algebraMap A K)
  let P : Ideal (MvPolynomial (Fin r) A) := (I.map g).comap g
  obtain ⟨j, hj⟩ := hf
  have hjK : algebraMap A K (f j) ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hj
  have hprime : (I.map g).IsPrime := by
    have hl := linear_prime_of_unit (fun i ↦ algebraMap A K (f i)) j
      (isUnit_iff_ne_zero.mpr hjK)
    simpa [I, g, Ideal.map_span, MvPolynomial.map_C, MvPolynomial.map_X] using
      (Ideal.span_singleton_prime hl.ne_zero).mpr hl
  have hp : P.IsPrime := hprime.comap g
  have hIP : I ≤ P := Ideal.le_comap_map
  have huniq : ∀ Q ∈ I.minimalPrimes, Q = P := by
    intro Q hQ
    have : Q.IsPrime := hQ.isPrime
    have hc := minimal_linear_contracts_zero f hJ Q hQ
    have hd : Disjoint ((nonZeroDivisors A).map (C (σ := Fin r)) :
        Set (MvPolynomial (Fin r) A)) Q := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨a, ha, rfl⟩ hmem
      exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) (hc a hmem)
    have he := minimal_eq_localized_linear (S := K) (nonZeroDivisors A)
      f j (isUnit_iff_ne_zero.mpr hjK) Q hQ hd
    simpa [P, I, g, Ideal.map_span, MvPolynomial.map_C, MvPolynomial.map_X] using he
  have hrad : I.radical = P := by
    rw [← Ideal.sInf_minimalPrimes]
    have hset : I.minimalPrimes = {P} := by
      apply Set.Subset.antisymm
      · intro Q hQ
        exact Set.mem_singleton_iff.mpr (huniq Q hQ)
      · obtain ⟨Q, hQ, _⟩ := Ideal.exists_minimalPrimes_le hIP
        simpa only [Set.singleton_subset_iff, ← huniq Q hQ] using hQ
    rw [hset, sInf_singleton]
  have : I.radical.IsPrime := hrad.symm ▸ hp
  have hn : (nilradical (MvPolynomial (Fin r) A ⧸ I)).IsPrime := by
    have hm : (I.radical.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk_surjective (I := I))
        (show RingHom.ker (Ideal.Quotient.mk I) ≤ I.radical by
          rw [Ideal.mk_ker]
          exact Ideal.le_radical)
    have he : I.radical.map (Ideal.Quotient.mk I) = nilradical (MvPolynomial (Fin r) A ⧸ I) := by
      rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
        (show RingHom.ker (Ideal.Quotient.mk I) ≤ I by rw [Ideal.mk_ker])]
      simp [nilradical]
    exact he ▸ hm
  exact PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr hn

end
