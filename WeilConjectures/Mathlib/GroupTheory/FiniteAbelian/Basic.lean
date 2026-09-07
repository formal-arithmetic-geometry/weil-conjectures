/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import WeilConjectures.Mathlib.Algebra.Ring.Equiv
public import WeilConjectures.Mathlib.Data.ZMod.QuotientGroup

/-!
# Finite abelian groups with prescribed torsion counts

A finite abelian group `G` that is killed by `n` and whose `m`-torsion has exactly `m ^ r`
elements for every `m` dividing `n` is a free `ZMod n`-module of rank `r`, i.e. isomorphic to
`(ZMod n) ^ r`.

The proof writes `G` as a direct sum of cyclic groups of prime power order using the structure
theorem `AddCommGroup.equiv_directSum_zmod_of_finite`, reads the hypothesis on the number of
`m`-torsion elements as a statement about the exponents appearing in that decomposition, and
reassembles the summands using the Chinese remainder theorem.

## Main results

- `AddCommGroup.nonempty_equiv_pi_zmod_of_card_torsion`
- `CommGroup.nonempty_equiv_pi_multiplicative_zmod_of_card_torsion` is the multiplicative version

## Implementation notes

The `m`-torsion of a group `G` is spelled as the subtype `{x : G // m • x = 0}`, and its
cardinality as `Nat.card`.
-/

@[expose] public section

open scoped DirectSum

/-- An additive equivalence identifies the `m`-torsion of the source with the `m`-torsion of
the target. -/
theorem Nat.card_nsmul_eq_zero_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (m : ℕ) :
    Nat.card {x : G // m • x = 0} = Nat.card {y : H // m • y = 0} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by simp [← map_nsmul])

/-- The `m`-torsion of a finite product of additive commutative monoids is the product of the
`m`-torsions of the factors. -/
theorem Nat.card_nsmul_eq_zero_pi {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommMonoid (M i)] (m : ℕ) :
    Nat.card {x : (∀ i, M i) // m • x = 0} = ∏ i, Nat.card {x : M i // m • x = 0} := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, congrFun x.2 i⟩
      invFun := fun x => ⟨fun i => (x i).1, funext fun i => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A finite abelian group `G` killed by `n` whose `m`-torsion has exactly `m ^ r` elements for
every `m` dividing `n` is isomorphic to `(ZMod n) ^ r`. -/
theorem AddCommGroup.nonempty_equiv_pi_zmod_of_card_torsion
    {G : Type*} [AddCommGroup G] [Finite G] {n r : ℕ} (hn : n ≠ 0)
    (hkill : ∀ x : G, n • x = 0)
    (hcard : ∀ m, m ∣ n → Nat.card {x : G // m • x = 0} = m ^ r) :
    Nonempty (G ≃+ (Fin r → ZMod n)) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  have : Fintype ι := hι
  have hne : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have F : G ≃+ (∀ i, ZMod (p i ^ e i)) := f.trans (DirectSum.addEquivProd _)
  -- every summand is killed by `n`
  have hdvd : ∀ i, p i ^ e i ∣ n := by
    intro i
    have h : n • (F (F.symm (fun _ => 1))) = 0 := by
      rw [← map_nsmul, hkill, map_zero]
    rw [F.apply_symm_apply] at h
    have h := congrFun h i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, mul_one] at h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  -- the counting hypothesis, read on the product
  have hcount : ∀ m, m ∣ n → ∏ i, Nat.gcd m (p i ^ e i) = m ^ r := by
    intro m hm
    rw [← hcard m hm, Nat.card_nsmul_eq_zero_congr F m, Nat.card_nsmul_eq_zero_pi]
    exact Finset.prod_congr rfl fun i _ => (ZMod.card_nsmul_eq_zero m).symm
  -- gcd of a prime power with a prime power
  have hgcd : ∀ {t : ℕ}, t.Prime → ∀ (k : ℕ) (i : ι),
      Nat.gcd (t ^ k) (p i ^ e i) = t ^ (if p i = t then min k (e i) else 0) := by
    intro t ht k i
    by_cases h : p i = t
    · subst h
      rcases le_total k (e i) with hk | hk
      · rw [if_pos rfl, min_eq_left hk, Nat.gcd_eq_left (pow_dvd_pow _ hk)]
      · rw [if_pos rfl, min_eq_right hk, Nat.gcd_eq_right (pow_dvd_pow _ hk)]
    · rw [if_neg h, pow_zero]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes ht (hp i)).mpr (Ne.symm h))
  have hsum : ∀ {t : ℕ}, t.Prime → ∀ k : ℕ, t ^ k ∣ n →
      (∑ i, if p i = t then min k (e i) else 0) = k * r := by
    intro t ht k hk
    have h := hcount (t ^ k) hk
    rw [Finset.prod_congr rfl (fun i _ => hgcd ht k i), Finset.prod_pow_eq_pow_sum,
      ← pow_mul] at h
    exact Nat.pow_right_injective ht.two_le h
  -- for each prime `t ∣ n`, exactly `r` summands are `t`-primary
  have hTcard : ∀ t ∈ n.primeFactors, Fintype.card {i : ι // e i ≠ 0 ∧ p i = t} = r := by
    intro t htn
    have ht := Nat.prime_of_mem_primeFactors htn
    have h := hsum ht 1 (by rw [pow_one]; exact Nat.dvd_of_mem_primeFactors htn)
    rw [one_mul] at h
    rw [Fintype.card_subtype, Finset.card_filter, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : p i = t
    · by_cases h2 : e i = 0
      · simp [h1, h2]
      · simp [h1, h2]
        omega
    · simp [h1]
  -- and each of them is `ZMod (t ^ a)` with `a` the multiplicity of `t` in `n`
  have hexp : ∀ t ∈ n.primeFactors, ∀ i : ι, e i ≠ 0 → p i = t →
      e i = n.factorization t := by
    intro t htn i hi hit
    have ht := Nat.prime_of_mem_primeFactors htn
    have hle : e i ≤ n.factorization t := by
      have h : p i ^ e i ∣ n := hdvd i
      rw [hit] at h
      exact (Nat.Prime.pow_dvd_iff_le_factorization ht hn).mp h
    have h := hsum ht (n.factorization t) (Nat.ordProj_dvd n t)
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => e i ≠ 0 ∧ p i = t),
        min (n.factorization t) (e i)
          = ∑ i, if p i = t then min (n.factorization t) (e i) else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ _) ?_]
      · exact Finset.sum_congr rfl fun j hj => (if_pos (Finset.mem_filter.mp hj).2.2).symm
      · intro j _ hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, ne_eq] at hj
        by_cases h3 : p j = t
        · have hj0 : e j = 0 := by by_contra hc; exact hj hc h3
          simp [h3, hj0]
        · simp [h3]
    have h3 : ∑ i ∈ Finset.univ.filter (fun i => e i ≠ 0 ∧ p i = t),
        min (n.factorization t) (e i)
          = ∑ _i ∈ Finset.univ.filter (fun i => e i ≠ 0 ∧ p i = t), n.factorization t := by
      rw [h2, h, Finset.sum_const, smul_eq_mul, mul_comm, ← Fintype.card_subtype, hTcard t htn]
    have := (Finset.sum_eq_sum_iff_of_le
      (fun j _ => min_le_left (n.factorization t) (e j))).mp h3 i
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hit⟩)
    omega
  -- the summands are indexed by the primes dividing `n`, with `r` summands for each
  have hmem : ∀ i : {x : ι // e x ≠ 0}, p i.1 ∈ n.primeFactors := fun i =>
    Nat.mem_primeFactors.mpr ⟨hp i.1, (dvd_pow_self (p i.1) i.2).trans (hdvd i.1), hn⟩
  set q : {x : ι // e x ≠ 0} → n.primeFactors := fun i => ⟨p i.1, hmem i⟩ with hq
  have hfib : ∀ t : n.primeFactors, Fintype.card {i : {x : ι // e x ≠ 0} // q i = t} = r := by
    intro t
    rw [Fintype.card_congr ((Equiv.subtypeEquivRight
        (q := fun i : {x : ι // e x ≠ 0} => p i.1 = (t : ℕ))
        (fun i => by rw [hq]; simp [Subtype.ext_iff])).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun x => e x ≠ 0) (fun x => p x = (t : ℕ))))]
    exact hTcard t t.2
  let Ψ : Fin r × n.primeFactors ≃ {x : ι // e x ≠ 0} :=
    (Equiv.prodComm _ _).trans <| (Equiv.sigmaEquivProd _ _).symm.trans <|
      (Equiv.sigmaCongrRight fun t => (Fintype.equivFinOfCardEq (hfib t)).symm).trans
        (Equiv.sigmaFiberEquiv q)
  have hΨ : ∀ z : Fin r × n.primeFactors, p (Ψ z).1 = (z.2 : ℕ) := by
    rintro ⟨j, t⟩
    exact congrArg Subtype.val ((Fintype.equivFinOfCardEq (hfib t)).symm j).2
  have hkey : ∀ z : Fin r × n.primeFactors,
      p (Ψ z).1 ^ e (Ψ z).1 = (z.2 : ℕ) ^ n.factorization (z.2 : ℕ) := fun z => by
    rw [hΨ z, hexp (z.2 : ℕ) z.2.2 (Ψ z).1 (Ψ z).2 (hΨ z)]
  have huniq : ∀ i : {x : ι // ¬(e x ≠ 0)}, Unique (ZMod (p i.1 ^ e i.1)) := by
    intro i
    have : Subsingleton (ZMod (p i.1 ^ e i.1)) :=
      ZMod.subsingleton_iff.2 (by rw [not_not.mp i.2, pow_zero])
    exact ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  have E1 : (∀ i, ZMod (p i ^ e i)) ≃+
      (∀ i : {x : ι // e x ≠ 0}, ZMod (p i.1 ^ e i.1)) ×
        (∀ i : {x : ι // ¬(e x ≠ 0)}, ZMod (p i.1 ^ e i.1)) :=
    (RingEquiv.piEquivPiSubtypeProd _ _).toAddEquiv
  have E2 : (∀ i : {x : ι // e x ≠ 0}, ZMod (p i.1 ^ e i.1)) ×
      (∀ i : {x : ι // ¬(e x ≠ 0)}, ZMod (p i.1 ^ e i.1)) ≃+
      (∀ i : {x : ι // e x ≠ 0}, ZMod (p i.1 ^ e i.1)) := AddEquiv.prodUnique
  have E3 : (∀ i : {x : ι // e x ≠ 0}, ZMod (p i.1 ^ e i.1)) ≃+
      (∀ z : Fin r × n.primeFactors, ZMod (p (Ψ z).1 ^ e (Ψ z).1)) :=
    (RingEquiv.piCongrLeft _ Ψ).symm.toAddEquiv
  have E4 : (∀ z : Fin r × n.primeFactors, ZMod (p (Ψ z).1 ^ e (Ψ z).1)) ≃+
      (∀ z : Fin r × n.primeFactors, ZMod ((z.2 : ℕ) ^ n.factorization (z.2 : ℕ))) :=
    (RingEquiv.piCongrRight fun z => ZMod.ringEquivCongr (hkey z)).toAddEquiv
  have E5 : (∀ z : Fin r × n.primeFactors, ZMod ((z.2 : ℕ) ^ n.factorization (z.2 : ℕ))) ≃+
      (Fin r → ∀ t : n.primeFactors, ZMod ((t : ℕ) ^ n.factorization (t : ℕ))) :=
    (RingEquiv.piCurryProd (ι := Fin r)
      fun t : n.primeFactors => ZMod ((t : ℕ) ^ n.factorization (t : ℕ))).toAddEquiv
  have E6 : (Fin r → ∀ t : n.primeFactors, ZMod ((t : ℕ) ^ n.factorization (t : ℕ))) ≃+
      (Fin r → ZMod n) :=
    AddEquiv.piCongrRight fun _ => (ZMod.equivPi n hn).symm.toAddEquiv
  exact ⟨F.trans (E1.trans (E2.trans (E3.trans (E4.trans (E5.trans E6)))))⟩

/-- A finite abelian group `G` killed by `n` all of whose `m`-th roots of unity are `m ^ r` in
number for every `m` dividing `n` is isomorphic to `(ZMod n) ^ r`.

This is the multiplicative version of
`AddCommGroup.nonempty_equiv_pi_zmod_of_card_torsion`. -/
theorem CommGroup.nonempty_equiv_pi_multiplicative_zmod_of_card_torsion
    {G : Type*} [CommGroup G] [Finite G] {n r : ℕ} (hn : n ≠ 0)
    (hkill : ∀ x : G, x ^ n = 1)
    (hcard : ∀ m, m ∣ n → Nat.card {x : G // x ^ m = 1} = m ^ r) :
    Nonempty (G ≃* (Fin r → Multiplicative (ZMod n))) := by
  obtain ⟨f⟩ := AddCommGroup.nonempty_equiv_pi_zmod_of_card_torsion (G := Additive G) hn
    (fun x => hkill x) (fun m hm => by
      rw [← hcard m hm]
      exact Nat.card_congr ((Additive.ofMul (α := G)).symm.subtypeEquiv fun x => by
        simp [← toMul_nsmul]))
  exact ⟨MulEquiv.toAdditive.symm
    (f.trans (MulEquiv.piMultiplicative fun _ : Fin r => ZMod n).toAdditiveRight)⟩
