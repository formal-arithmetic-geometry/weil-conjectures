/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Filtration

/-!
# Rigidity of congruence kernels with coprime finite images

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, p. 3, integral representation
context; the algebraic corollary and its proof are the agent supplement in the DAG
(blueprint: lem-sfb-coprime-congruence-kernel-rigidity).

The reduction homomorphism is the canonical entrywise quotient map. No topology is used.
-/

@[expose] public section

universe u v

namespace Padic

/-- Entrywise reduction of an integral matrix representation modulo the `n`th power
of the chosen uniformizer. The formula also defines level zero, but the rigidity
statement only concerns positive levels.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, p. 3, integral representation
context; agent algebraic supplement, definition of `A_n`
(blueprint: lem-sfb-coprime-congruence-kernel-rigidity). -/
noncomputable def coefficientExtensionRepresentationReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (H : Type v) [Group H] (r : ℕ)
    (A : H →* Matrix.GeneralLinearGroup (Fin r) (coefficientExtensionIntegers l E))
    (n : ℕ) : H →* Matrix.GeneralLinearGroup (Fin r) (coefficientExtensionRing l E n) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (coefficientExtensionIdeal l E n))).comp A

private theorem reduction_eq_one_iff {R : Type*} [CommRing R] {r : ℕ}
    (I : Ideal R) (a : Matrix.GeneralLinearGroup (Fin r) R) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) a = 1 ↔
      ∀ i j, (a : Matrix (Fin r) (Fin r) R) i j - (1 : Matrix (Fin r) (Fin r) R) i j ∈ I := by
  rw [Matrix.GeneralLinearGroup.ext_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro j
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]

private theorem congruence_power {R : Type*} [CommRing R] {r : ℕ}
    (I : Ideal R) (p n : ℕ) (hn : 1 ≤ n) (hp : (p : R) ∈ I)
    (a : Matrix.GeneralLinearGroup (Fin r) R)
    (ha : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ n)) a = 1) :
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ (n + 1))) a) ^ p = 1 := by
  classical
  let q := Ideal.Quotient.mk (I ^ (n + 1))
  let B : Matrix (Fin r) (Fin r) R := (a : Matrix (Fin r) (Fin r) R) - 1
  let X : Matrix (Fin r) (Fin r) (R ⧸ I ^ (n + 1)) := B.map q
  have hB : ∀ i j, B i j ∈ I ^ n := (reduction_eq_one_iff (I ^ n) a).mp ha
  have hX : X * X = 0 := by
    ext i j
    change ∑ k, q (B i k) * q (B k j) = 0
    apply Finset.sum_eq_zero
    intro k _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.pow_le_pow_right (show n + 1 ≤ n + n by omega)
    rw [pow_add]
    exact Ideal.mul_mem_mul (hB i k) (hB k j)
  have hpX : p • X = 0 := by
    ext i j
    change p • q (B i j) = 0
    rw [nsmul_eq_mul, ← map_natCast q, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    rw [pow_succ']
    exact Ideal.mul_mem_mul hp (hB i j)
  have hpow (m : ℕ) : (1 + X) ^ m = 1 + m • X := by
    induction m with
    | zero => simp
    | succ m hm =>
      calc
        (1 + X) ^ (m + 1) = (1 + X) ^ m * (1 + X) := pow_succ _ _
        _ = (1 + m • X) * (1 + X) := by rw [hm]
        _ = 1 + (m + 1) • X := by
          simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hX,
            nsmul_zero, add_zero, succ_nsmul]
          abel
  have hval : ((Matrix.GeneralLinearGroup.map q a) :
      Matrix (Fin r) (Fin r) (R ⧸ I ^ (n + 1))) = 1 + X := by
    ext i j
    simp [X, B, q, Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
  apply Units.ext
  change ((Matrix.GeneralLinearGroup.map q a :
    Matrix (Fin r) (Fin r) (R ⧸ I ^ (n + 1))) ^ p) = 1
  rw [hval, hpow, hpX, add_zero]

/-- If every positive-level congruence image has finite order coprime to `l`, its
kernel equals both the first congruence kernel and the integral representation kernel.
This includes rank zero and arbitrary abstract groups.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, p. 3, integral representation
context; agent algebraic supplement, Steps 1--5
(blueprint: lem-sfb-coprime-congruence-kernel-rigidity).

Proof:
1. The coefficient convention and `lem-weil-l-adic-extension-integers-dvr` give
   a Noetherian local integer ring, a proper ideal `I = (π)`, and `l ∈ I`, using
   the normalized p-adic absolute value (`def-weil-l-adic-numbers`).
2. For `h ∈ K_n`, every entry of `B = A(h) - I_r` belongs to `I^n`. Modulo
   `I^(n+1)`, its image `X` satisfies `X² = 0` since `2n ≥ n+1`, and `l X = 0`.
   Induction on `m` gives `(I + X)^m = I + m X`, hence `A_(n+1)(h)^l = I`.
   Only matrix multiplication (`def-weil-matrix`) and quotient arithmetic are used.
3. Induct on positive `n` to obtain `K_1 = K_n`. The induction step uses Step 2
   and the injectivity of the `l`th power map on the finite image `Q_(n+1)`:
   `lem-sfb-finite-matrix-group-coprime-power`, namely
   `Nat.Coprime.pow_left_bijective`. The reverse inclusion follows by reduction
   modulo `π`.
4. An entry of `A(h) - I_r` for `h ∈ K_1` lies in every `I^n`, including the
   vacuous level zero. Krull's intersection theorem for Noetherian local rings,
   `Ideal.iInf_pow_eq_bot_of_isLocalRing`, makes this intersection zero since
   `I` is proper. Thus all entries vanish and `h ∈ ker A`.
5. Conversely an element of `ker A` reduces to the identity at every level.
   Combine this with Steps 3--4. For rank zero the empty matrix is the identity,
   so every kernel is the whole group; the entrywise argument is vacuous.
-/
theorem coprime_congruence_kernel_rigidity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (H : Type v) [Group H] (r : ℕ)
    (A : H →* Matrix.GeneralLinearGroup (Fin r) (coefficientExtensionIntegers l E))
    (hfinite : ∀ n : ℕ, 1 ≤ n →
      Finite (coefficientExtensionRepresentationReduction l E H r A n).range)
    (hcoprime : ∀ n : ℕ, 1 ≤ n →
      (Nat.card (coefficientExtensionRepresentationReduction l E H r A n).range).Coprime l) :
    ∀ n : ℕ, 1 ≤ n →
      (coefficientExtensionRepresentationReduction l E H r A 1).ker =
        (coefficientExtensionRepresentationReduction l E H r A n).ker ∧
      (coefficientExtensionRepresentationReduction l E H r A n).ker = A.ker := by
  classical
  let R := coefficientExtensionIntegers l E
  let I : Ideal R := Ideal.span {coefficientExtensionUniformizer l E}
  let f (n : ℕ) := coefficientExtensionRepresentationReduction l E H r A n
  have hs := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : I = coefficientExtensionMaximalIdeal l E :=
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  rcases hs with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr,
    hpid, hm0, hprime, hfiniteResidue, hr, hexists, hassoc, hfactor⟩
  have : IsLocalRing R := hlocal
  have : IsDiscreteValuationRing R := hdvr
  have hproper : I ≠ ⊤ := by rw [hgen]; exact hmax.ne_top
  have hl : (l : R) ∈ I := by
    rw [hgen]
    apply (hm _).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hentry (n : ℕ) (h : H) :
      f n h = 1 ↔ ∀ i j, (A h : Matrix (Fin r) (Fin r) R) i j -
        (1 : Matrix (Fin r) (Fin r) R) i j ∈ I ^ n :=
    reduction_eq_one_iff (I ^ n) (A h)
  have hback (n : ℕ) (hn : 1 ≤ n) (h : H) (hh : f n h = 1) : f 1 h = 1 := by
    apply (hentry 1 h).mpr
    intro i j
    exact Ideal.pow_le_pow_right hn ((hentry n h).mp hh i j)
  have hforward (n : ℕ) (hn : 1 ≤ n) (h : H) (hh : f 1 h = 1) : f n h = 1 := by
    induction n, hn using Nat.le_induction with
    | base => exact hh
    | succ n hn ih =>
      have : Finite (f (n + 1)).range := hfinite (n + 1) (by omega)
      have hp : (f (n + 1) h) ^ l = 1 := congruence_power I l n hn hl (A h) ih
      let x : (f (n + 1)).range := ⟨f (n + 1) h, ⟨h, rfl⟩⟩
      have hx : x ^ l = 1 := Subtype.ext hp
      have heq : x = 1 := (hcoprime (n + 1) (by omega)).pow_left_bijective.injective
        (hx.trans (one_pow l).symm)
      exact congrArg Subtype.val heq
  have hintegral (h : H) (hh : f 1 h = 1) : A h = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply sub_eq_zero.mp
    have hx : (A h : Matrix (Fin r) (Fin r) R) i j -
        (1 : Matrix (Fin r) (Fin r) R) i j ∈ ⨅ m : ℕ, I ^ m := by
      apply Ideal.mem_iInf.mpr
      intro m
      by_cases hm : 1 ≤ m
      · exact (hentry m h).mp (hforward m hm h hh) i j
      · have : m = 0 := by omega
        simp [this]
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I hproper] at hx
    exact hx
  intro n hn
  constructor
  · ext h
    exact ⟨hforward n hn h, hback n hn h⟩
  · ext h
    change f n h = 1 ↔ A h = 1
    exact ⟨fun hh => hintegral h (hback n hn h hh), fun hh => by
      change (Matrix.GeneralLinearGroup.map _ (A h)) = 1
      rw [hh, map_one]⟩

end Padic
