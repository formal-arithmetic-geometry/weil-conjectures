/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.PurelyInseparable.Exponent

/-!
# Powers in the base after localization

Let `A' → E` be a finite extension of Noetherian domains whose fraction field extension
`K' → L` is finite purely inseparable. After inverting a suitable nonzero `s ∈ A'`, the
inclusion `A'[1/s] → E ⊗[A'] A'[1/s]` is surjective in characteristic zero, and in
characteristic `p` every element of `E ⊗[A'] A'[1/s]` has a `p`-power in `A'[1/s]`.

## Implementation details

Choose finitely many `A'`-module generators `e_i` of `E` and a uniform exponent `N` of the
purely inseparable extension. Writing `e_i^(q^N) = b_i / t_i` in `K'`, with
`q = ringExpChar K'`, and taking `s = ∏ t_i`, the generators' powers lie in the localized base.
The statement for all elements follows by span and tensor induction, since `x ↦ x^(q^N)` is
additive. This also covers `q = 1` and `N = 0`; no normality assumption on `A'` is used.

## References

* Stacks Project, Algebra, Section 0BR5 and Lemma 0BR8
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace RingTheory

/--
There are a nonzero `s : A'`, a finite set `g` of `A'`-module generators of `E` and an
exponent `N` such that `(e ⊗ 1)^(q^N)` lies in the image of `A'[1/s]` for every `e ∈ g`,
where `q = ringExpChar K'`.
-/
private theorem localized_generator_powers
    (A' : Type u) (K' : Type v) (E : Type w) (L : Type z)
    [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [Field K'] [Field L] [CommRing E] [IsDomain E]
    [Algebra A' E] [Module.Finite A' E]
    [Algebra A' K'] [Algebra E L] [Algebra K' L] [Algebra A' L]
    [IsScalarTower A' E L] [IsScalarTower A' K' L]
    [Module.Finite K' L] [IsPurelyInseparable K' L]
    [IsFractionRing A' K'] [IsFractionRing E L] :
    ∃ s : A', s ≠ 0 ∧ ∃ g : Finset E,
      Submodule.span A' (g : Set E) = ⊤ ∧ ∃ N : ℕ,
        ∀ e ∈ g, ∃ a : Localization.Away s,
          Algebra.TensorProduct.includeRight (R := A') (A := E) a =
            (e ⊗ₜ[A'] (1 : Localization.Away s)) ^ (ringExpChar K' ^ N) := by
  classical
  obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := A') (M := E)
  obtain ⟨N, hN⟩ := IsPurelyInseparable.HasExponent.has_exponent (K := K') (L := L)
  have hden (e : E) : ∃ b t : A', t ≠ 0 ∧
      algebraMap A' E t * e ^ (ringExpChar K' ^ N) = algebraMap A' E b := by
    obtain ⟨c, hc⟩ := hN (algebraMap E L e)
    obtain ⟨⟨b, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors A') c
    refine ⟨b, t, mem_nonZeroDivisors_iff_ne_zero.mp t.property, ?_⟩
    apply IsFractionRing.injective E L
    simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    rw [← hc]
    have ht' := congrArg (algebraMap K' L) ht
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply, mul_comm] using ht'
  choose b t ht hden using hden
  let s := ∏ e ∈ g, t e
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun e he ↦ ht e)
  refine ⟨s, hs, g, hg, N, ?_⟩
  intro e he
  have hdvd : t e ∣ s := Finset.dvd_prod_of_mem t he
  have hu : IsUnit (algebraMap A' (Localization.Away s) (t e)) :=
    IsLocalization.Away.isUnit_of_dvd s hdvd
  obtain ⟨v, hv⟩ := hu
  refine ⟨algebraMap A' (Localization.Away s) (b e) * ↑(v⁻¹), ?_⟩
  let ι : Localization.Away s →ₐ[A'] E ⊗[A'] Localization.Away s :=
    Algebra.TensorProduct.includeRight
  let j : E →ₐ[A'] E ⊗[A'] Localization.Away s := Algebra.TensorProduct.includeLeft
  have hm : ι (algebraMap A' (Localization.Away s) (t e)) * (j e) ^
      (ringExpChar K' ^ N) = ι (algebraMap A' (Localization.Away s) (b e)) := by
    have hh := congrArg j (hden e)
    simpa only [map_mul, map_pow, AlgHom.commutes] using hh
  change ι _ = (j e) ^ (ringExpChar K' ^ N)
  rw [map_mul, ← hm, mul_assoc, mul_comm ((j e) ^ _) (ι _), ← mul_assoc,
    ← map_mul, ← hv]
  simp

/-- Extend generator powers to the tensor product by span and tensor induction. -/
private theorem powers_from_generators
    (A : Type u) (E : Type w) (B : Type v)
    [CommRing A] [CommRing E] [CommRing B] [Algebra A E] [Algebra A B]
    (g : Finset E) (hg : Submodule.span A (g : Set E) = ⊤)
    (k : ℕ) (hk : k ≠ 0)
    (hadd : ∀ x y : E ⊗[A] B, (x + y) ^ k = x ^ k + y ^ k)
    (hgen : ∀ e ∈ g, ∃ b : B,
      Algebra.TensorProduct.includeRight (R := A) (A := E) b =
        (e ⊗ₜ[A] (1 : B)) ^ k) :
    ∀ x : E ⊗[A] B, ∃ b : B,
      Algebra.TensorProduct.includeRight (R := A) (A := E) b = x ^ k := by
  let ι : B →ₐ[A] E ⊗[A] B := Algebra.TensorProduct.includeRight
  have he (e : E) : ∃ b : B, ι b = (e ⊗ₜ[A] (1 : B)) ^ k := by
    have hmem : e ∈ Submodule.span A (g : Set E) := by rw [hg]; trivial
    induction hmem using Submodule.span_induction with
    | mem e he => exact hgen e he
    | zero => exact ⟨0, by simp [hk, ι]⟩
    | add e f _ _ he hf =>
      obtain ⟨b, hb⟩ := he
      obtain ⟨c, hc⟩ := hf
      exact ⟨b + c, by simp only [map_add, TensorProduct.add_tmul, hadd, hb, hc]⟩
    | smul a e _ he =>
      obtain ⟨b, hb⟩ := he
      refine ⟨(algebraMap A B a) ^ k * b, ?_⟩
      rw [map_mul, map_pow, hb]
      have hm : (a • e) ⊗ₜ[A] (1 : B) = ι (algebraMap A B a) * (e ⊗ₜ[A] 1) := by
        simp [ι, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul,
          Algebra.algebraMap_eq_smul_one]
      rw [hm, mul_pow]
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨b + c, by simp only [map_add, hadd, hb, hc]⟩
  | tmul e b =>
    obtain ⟨c, hc⟩ := he e
    refine ⟨c * b ^ k, ?_⟩
    rw [map_mul, hc, map_pow]
    have hm : e ⊗ₜ[A] b = (e ⊗ₜ[A] (1 : B)) * ι b := by
      simp [ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hm, mul_pow]

/--
Let `A' → E` be a finite extension of Noetherian domains with finite purely inseparable
fraction field extension `K' → L`. There is a nonzero `s : A'` such that
`A'[1/s] → E ⊗[A'] A'[1/s]` is surjective if `K'` has characteristic zero, and such that every
element of `E ⊗[A'] A'[1/s]` has some `p^n`-th power in the image of `A'[1/s]` if `K'` has
prime characteristic `p`.
-/
theorem power_in_base_after_localization
    (A' : Type u) (K' : Type v) (E : Type w) (L : Type z)
    [CommRing A'] [IsDomain A'] [IsNoetherianRing A']
    [Field K'] [Field L]
    [CommRing E] [IsDomain E]
    [Algebra A' E] [Module.Finite A' E]
    [Algebra A' K'] [Algebra E L] [Algebra K' L] [Algebra A' L]
    [IsScalarTower A' E L] [IsScalarTower A' K' L]
    [Module.Finite K' L] [IsPurelyInseparable K' L]
    [IsFractionRing A' K'] [IsFractionRing E L] :
    ∃ s : A', s ≠ 0 ∧
      (CharZero K' → Function.Surjective
        (Algebra.TensorProduct.includeRight (R := A') (A := E)
          (B := Localization.Away s) :
          Localization.Away s → E ⊗[A'] Localization.Away s)) ∧
      (∀ p : ℕ, Nat.Prime p → CharP K' p →
        ∀ x : E ⊗[A'] Localization.Away s, ∃ n : ℕ, ∃ a : Localization.Away s,
          Algebra.TensorProduct.includeRight (R := A') (A := E)
            (B := Localization.Away s) a = x ^ (p ^ n)) := by
  classical
  obtain ⟨s, hs, g, hg, N, hgen⟩ := localized_generator_powers A' K' E L
  refine ⟨s, hs, ?_, ?_⟩
  · intro hzero
    have : CharZero K' := hzero
    have hgen' : ∀ e ∈ g, ∃ a : Localization.Away s,
        Algebra.TensorProduct.includeRight (R := A') (A := E) a =
          (e ⊗ₜ[A'] (1 : Localization.Away s)) ^ 1 := by
      simpa using hgen
    intro x
    obtain ⟨a, ha⟩ := powers_from_generators A' E (Localization.Away s) g hg 1
      (by decide) (by intros; simp) hgen' x
    exact ⟨a, by simpa only [pow_one] using ha⟩
  · intro p hp hchar x
    have : CharP K' p := hchar
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have : ExpChar K' p := inferInstance
    have hq : ringExpChar K' = p := ringExpChar.eq K' p
    have hgen' : ∀ e ∈ g, ∃ a : Localization.Away s,
        Algebra.TensorProduct.includeRight (R := A') (A := E) a =
          (e ⊗ₜ[A'] (1 : Localization.Away s)) ^ (p ^ N) := by
      simpa only [hq] using hgen
    rcases subsingleton_or_nontrivial (E ⊗[A'] Localization.Away s) with hsub | hn
    · have : Subsingleton (E ⊗[A'] Localization.Away s) := hsub
      exact ⟨0, 0, Subsingleton.elim _ _⟩
    · have : Nontrivial (E ⊗[A'] Localization.Away s) := hn
      have : CharP A' p := (algebraMap A' K').charP (IsFractionRing.injective A' K') p
      have : CharP (E ⊗[A'] Localization.Away s) p :=
        CharP.of_ringHom_of_ne_zero (algebraMap A' _) p hp.ne_zero
      obtain ⟨a, ha⟩ := powers_from_generators A' E (Localization.Away s) g hg (p ^ N)
        (pow_ne_zero _ hp.ne_zero) (fun x y ↦ add_pow_char_pow x y p N) hgen' x
      exact ⟨N, a, ha⟩

end RingTheory
