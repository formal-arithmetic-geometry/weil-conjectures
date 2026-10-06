/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Divisible
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The torsion of a divisible abelian group

If `D` is a divisible abelian group whose `ℓ`-torsion is finite of order `ℓ ^ r` for a prime
`ℓ`, then its `ℓ ^ n`-torsion is free of rank `r` over `ℤ / ℓ ^ n` for every `n`. This is
the structural input that makes the Tate module of an abelian variety a free `ℤ_[ℓ]`-module.

## Main statements

- `AddSubgroup.nonempty_addEquiv_torsionBy_of_natCard_eq`: `D[ℓ ^ n] ≃+ (Fin r → ZMod (ℓ ^ n))`.
- `AddSubgroup.nonempty_addEquiv_torsionBy_of_forall_prime`: if `|D[ℓ]| = ℓ ^ r` for every
  prime `ℓ ∣ n`, then `D[n] ≃+ (Fin r → ZMod n)`.

## Implementation notes

Instead of the classification of finite abelian `ℓ`-groups used in the blueprint, we choose an
`𝔽_ℓ`-basis `e` of `D[ℓ]`, lift it along multiplication by `ℓ ^ (n - 1)` to `y` using
divisibility, and show by induction on `n` that `c ↦ ∑ i, c i • y i` identifies
`(ℤ / ℓ ^ n) ^ r` with `D[ℓ ^ n]`.
-/

@[expose] public section

open scoped AddSubgroup

namespace AddSubgroup

section

variable {D ι : Type*} [AddCommGroup D] [Fintype ι]

/-- Let `e` be a family in an abelian group which is a "basis of the `ℓ`-torsion with integer
coefficients", i.e. integer relations among the `e i` have coefficients divisible by `ℓ`, and
every element killed by `ℓ` is an integer combination of the `e i`. If `ℓ ^ k • z i = e i`,
then integer relations among the `z i` have coefficients divisible by `ℓ ^ (k + 1)`, and every
element killed by `ℓ ^ (k + 1)` is an integer combination of the `z i`. -/
private theorem sum_zsmul_dvd_and_exists_of_pow_zsmul_eq (ℓ : ℤ) (e : ι → D)
    (he : ∀ c : ι → ℤ, ∑ i, c i • e i = 0 → ∀ i, ℓ ∣ c i)
    (he' : ∀ x : D, ℓ • x = 0 → ∃ c : ι → ℤ, x = ∑ i, c i • e i) (k : ℕ) (z : ι → D)
    (hz : ∀ i, ℓ ^ k • z i = e i) :
    (∀ c : ι → ℤ, ∑ i, c i • z i = 0 → ∀ i, ℓ ^ (k + 1) ∣ c i) ∧
      ∀ x : D, ℓ ^ (k + 1) • x = 0 → ∃ c : ι → ℤ, x = ∑ i, c i • z i := by
  induction k generalizing z with
  | zero =>
    obtain rfl : z = e := funext fun i ↦ by simpa using hz i
    simpa using ⟨he, he'⟩
  | succ k ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (fun i ↦ ℓ • z i) fun i ↦ by rw [smul_smul, ← pow_succ, hz]
    refine ⟨fun c hc ↦ ?_, fun x hx ↦ ?_⟩
    · have h₁ : ∀ i, ℓ ∣ c i := he c <| by
        simp_rw [← hz, smul_comm (c _), ← Finset.smul_sum, hc, smul_zero]
      choose d hd using h₁
      have h₂ := ih₁ d <| by
        simp_rw [smul_smul, mul_comm _ ℓ, ← hd, hc]
      intro i
      rw [hd i, pow_succ' ℓ (k + 1)]
      exact mul_dvd_mul_left ℓ (h₂ i)
    · obtain ⟨c, hc⟩ := ih₂ (ℓ • x) <| by rw [smul_smul, ← pow_succ, hx]
      obtain ⟨a, ha⟩ := he' (x - ∑ i, c i • z i) <| by
        rw [smul_sub, hc, Finset.smul_sum]
        simp_rw [smul_comm ℓ (c _), sub_self]
      refine ⟨fun i ↦ c i + a i * ℓ ^ (k + 1), ?_⟩
      simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, hz, ← ha]
      abel

end

/-- Blueprint `sk-prop-av-divisible-structure`: The torsion of a divisible group.

This is also the blueprint lemma `lem-sc-divisible-group-structure`.

Let `D` be a divisible abelian group, let `ℓ` be a prime and suppose that the `ℓ`-torsion of
`D` is finite of order `ℓ ^ r`. Then for every `n` the `ℓ ^ n`-torsion of `D` is isomorphic
to `(ℤ / ℓ ^ n) ^ r`. -/
theorem nonempty_addEquiv_torsionBy_of_natCard_eq (D : Type*) [AddCommGroup D]
    [DivisibleBy D ℤ] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (hr : Nat.card D[(ℓ : ℤ)] = ℓ ^ r) (n : ℕ) :
    Nonempty (D[((ℓ : ℤ) ^ n)] ≃+ (Fin r → ZMod (ℓ ^ n))) := by
  have hℓ : ℓ.Prime := Fact.out
  -- an `𝔽_ℓ`-basis `e` of `D[ℓ]`
  let _ : Module (ZMod ℓ) D[(ℓ : ℤ)] := torsionBy.zmodModule
  have : Finite D[(ℓ : ℤ)] :=
    Nat.finite_of_card_ne_zero (by rw [hr]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fintype D[(ℓ : ℤ)] := Fintype.ofFinite _
  have hrank : Module.finrank (ZMod ℓ) D[(ℓ : ℤ)] = r := by
    have h := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := D[(ℓ : ℤ)])
    rw [← Nat.card_eq_fintype_card, hr, ZMod.card] at h
    exact (Nat.pow_right_injective hℓ.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod ℓ) D[(ℓ : ℤ)] hrank
  let e : Fin r → D := fun i ↦ b i
  have he : ∀ c : Fin r → ℤ, ∑ i, c i • e i = 0 → ∀ i, (ℓ : ℤ) ∣ c i := by
    intro c hc i
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 <|
      Fintype.linearIndependent_iff.1 b.linearIndependent (fun i ↦ (c i : ZMod ℓ))
        (Subtype.ext ?_) i
    simpa [Int.cast_smul_eq_zsmul] using hc
  have he' : ∀ x : D, (ℓ : ℤ) • x = 0 → ∃ c : Fin r → ℤ, x = ∑ i, c i • e i := by
    intro x hx
    refine ⟨fun i ↦ (b.repr ⟨x, hx⟩ i).cast, ?_⟩
    conv_lhs => rw [show x = ((⟨x, hx⟩ : D[(ℓ : ℤ)]) : D) from rfl, ← b.sum_repr ⟨x, hx⟩]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [← ZMod.intCast_zmod_cast (b.repr ⟨x, hx⟩ i), Int.cast_smul_eq_zsmul]
    rfl
  cases n with
  | zero =>
    rw [pow_zero, pow_zero]
    have : Subsingleton D[(1 : ℤ)] := ⟨fun x y ↦ Subtype.ext <| by
      have hx := (Submodule.mem_torsionBy_iff _ _).1 x.2
      have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
      rw [one_smul] at hx hy
      rw [hx, hy]⟩
    exact ⟨(AddEquiv.ofBijective (0 : D[(1 : ℤ)] →+ (Fin r → ZMod 1))
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩)⟩
  | succ m =>
    -- lifts `y i` of `e i` along multiplication by `ℓ ^ m`
    let y : Fin r → D := fun i ↦ DivisibleBy.div (e i) ((ℓ : ℤ) ^ m)
    have hy : ∀ i, (ℓ : ℤ) ^ m • y i = e i := fun i ↦
      DivisibleBy.div_cancel _ (pow_ne_zero _ (Int.natCast_ne_zero.2 hℓ.ne_zero))
    obtain ⟨hinj, hsurj⟩ := sum_zsmul_dvd_and_exists_of_pow_zsmul_eq _ e he he' m y hy
    rw [show (ℓ : ℤ) ^ (m + 1) = ((ℓ ^ (m + 1) : ℕ) : ℤ) by push_cast; rfl]
    let _ : Module (ZMod (ℓ ^ (m + 1))) D[((ℓ ^ (m + 1) : ℕ) : ℤ)] := torsionBy.zmodModule
    have hyN : ∀ i, y i ∈ D[((ℓ ^ (m + 1) : ℕ) : ℤ)] := fun i ↦ by
      refine (Submodule.mem_torsionBy_iff _ _).2 ?_
      push_cast
      rw [pow_succ', mul_smul, hy]
      exact (b i).2
    let f := Fintype.linearCombination (ZMod (ℓ ^ (m + 1))) fun i ↦
      (⟨y i, hyN i⟩ : D[((ℓ ^ (m + 1) : ℕ) : ℤ)])
    have hf : ∀ c : Fin r → ℤ, (f fun i ↦ (c i : ZMod (ℓ ^ (m + 1))) : D) = ∑ i, c i • y i := by
      intro c
      simp [f, Fintype.linearCombination_apply, Int.cast_smul_eq_zsmul]
    have hf_inj : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).2 fun c hc ↦ funext fun i ↦ ?_
      rw [← funext fun i ↦ ZMod.intCast_zmod_cast (c i)] at hc ⊢
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
      push_cast
      have hc' := congrArg Subtype.val hc
      rw [hf] at hc'
      exact hinj _ hc' i
    have hf_surj : Function.Surjective f := by
      rintro ⟨x, hx⟩
      have hx' := (Submodule.mem_torsionBy_iff _ _).1 hx
      push_cast at hx'
      obtain ⟨c, rfl⟩ := hsurj x hx'
      exact ⟨fun i ↦ c i, Subtype.ext (hf c)⟩
    exact ⟨(AddEquiv.ofBijective f.toAddMonoidHom ⟨hf_inj, hf_surj⟩).symm⟩

/-- For coprime `a` and `b`, the `a * b`-torsion of an abelian group is the product of its
`a`-torsion and its `b`-torsion, via `x ↦ (b • x, a • x)`. -/
theorem nonempty_addEquiv_torsionBy_mul_prod (D : Type*) [AddCommGroup D] {a b : ℕ}
    (hab : a.Coprime b) :
    Nonempty (D[((a * b : ℕ) : ℤ)] ≃+ D[(a : ℤ)] × D[(b : ℤ)]) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  let f : D[((a * b : ℕ) : ℤ)] →+ D[(a : ℤ)] × D[(b : ℤ)] :=
    { toFun x := (⟨(b : ℤ) • x.1, by
          have := (Submodule.mem_torsionBy_iff _ _).1 x.2
          refine (Submodule.mem_torsionBy_iff _ _).2 ?_
          rw [smul_smul, ← this]
          push_cast
          ring_nf⟩,
        ⟨(a : ℤ) • x.1, by
          have := (Submodule.mem_torsionBy_iff _ _).1 x.2
          refine (Submodule.mem_torsionBy_iff _ _).2 ?_
          rw [smul_smul, ← this]
          push_cast
          ring_nf⟩)
      map_zero' := by ext <;> simp
      map_add' x y := by ext <;> simp }
  refine ⟨AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun x hx ↦ ?_, ?_⟩⟩
  · have h₁ : (b : ℤ) • (x : D) = 0 := congrArg (fun y ↦ (y.1 : D)) hx
    have h₂ : (a : ℤ) • (x : D) = 0 := congrArg (fun y ↦ (y.2 : D)) hx
    refine Subtype.ext ?_
    rw [ZeroMemClass.coe_zero, ← one_smul ℤ (x : D), ← huv, add_smul, mul_smul, mul_smul, h₁, h₂,
      smul_zero, smul_zero, add_zero]
  · rintro ⟨y, z⟩
    have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
    have hz := (Submodule.mem_torsionBy_iff _ _).1 z.2
    refine ⟨⟨v • (y : D) + u • (z : D), (Submodule.mem_torsionBy_iff _ _).2 ?_⟩, ?_⟩
    · push_cast
      rw [smul_add, smul_smul, smul_smul, show (a : ℤ) * b * v = b * v * a by ring,
        show (a : ℤ) * b * u = a * u * b by ring, mul_smul, mul_smul (a * u), hy, hz, smul_zero,
        smul_zero, add_zero]
    · have hy' : (y : D) = (v * b) • (y : D) := by
        conv_lhs => rw [← one_smul ℤ (y : D), ← huv]
        rw [add_smul, mul_smul u, hy, smul_zero, zero_add]
      have hz' : (z : D) = (u * a) • (z : D) := by
        conv_lhs => rw [← one_smul ℤ (z : D), ← huv]
        rw [add_smul, mul_smul v, hz, smul_zero, add_zero]
      ext
      · change (b : ℤ) • (v • (y : D) + u • (z : D)) = y
        rw [smul_add, smul_smul, smul_smul, mul_comm (b : ℤ) u, mul_smul u, hz, smul_zero,
          add_zero, mul_comm, ← hy']
      · change (a : ℤ) • (v • (y : D) + u • (z : D)) = z
        rw [smul_add, smul_smul, smul_smul, mul_comm (a : ℤ) v, mul_smul v, hy, smul_zero,
          zero_add, mul_comm, ← hz']

/-- The Chinese remainder step of blueprint `sk-prop-av-ntorsion-etale`.

Let `D` be a divisible abelian group and suppose that for every prime `ℓ` dividing `n ≠ 0` the
`ℓ`-torsion of `D` has order `ℓ ^ r`. Then the `n`-torsion of `D` is isomorphic to
`(ℤ / n) ^ r`: for prime powers this is
`AddSubgroup.nonempty_addEquiv_torsionBy_of_natCard_eq`, and the general case follows by the
Chinese remainder theorem. -/
theorem nonempty_addEquiv_torsionBy_of_forall_prime (D : Type*) [AddCommGroup D]
    [DivisibleBy D ℤ] (r : ℕ) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → Nat.card D[(ℓ : ℤ)] = ℓ ^ r) :
    Nonempty (D[(n : ℤ)] ≃+ (Fin r → ZMod n)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow ℓ e hℓ he =>
    have : Fact ℓ.Prime := ⟨hℓ⟩
    push_cast
    exact nonempty_addEquiv_torsionBy_of_natCard_eq D ℓ r (h ℓ hℓ (dvd_pow_self ℓ he.ne')) e
  | zero => exact absurd rfl hn
  | one =>
    have : Subsingleton D[((1 : ℕ) : ℤ)] := ⟨fun x y ↦ Subtype.ext <| by
      have hx := (Submodule.mem_torsionBy_iff _ _).1 x.2
      have hy := (Submodule.mem_torsionBy_iff _ _).1 y.2
      simp only [Nat.cast_one, one_smul] at hx hy
      rw [hx, hy]⟩
    exact ⟨AddEquiv.ofBijective (0 : D[((1 : ℕ) : ℤ)] →+ (Fin r → ZMod 1))
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨ea⟩ := iha (by omega) fun ℓ hℓ hd ↦ h ℓ hℓ (hd.mul_right b)
    obtain ⟨eb⟩ := ihb (by omega) fun ℓ hℓ hd ↦ h ℓ hℓ (hd.mul_left a)
    obtain ⟨e⟩ := nonempty_addEquiv_torsionBy_mul_prod D hab
    let arrow : (Fin r → ZMod a) × (Fin r → ZMod b) ≃+ (Fin r → ZMod a × ZMod b) :=
      { (Equiv.arrowProdEquivProdArrow _ _ _).symm with map_add' := fun _ _ ↦ rfl }
    exact ⟨e.trans ((ea.prodCongr eb).trans (arrow.trans
      (AddEquiv.piCongrRight fun _ ↦ (ZMod.chineseRemainder hab).toAddEquiv).symm))⟩

end AddSubgroup
