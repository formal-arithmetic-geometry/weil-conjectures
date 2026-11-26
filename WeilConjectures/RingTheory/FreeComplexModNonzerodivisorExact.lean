/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Exactness after reduction by a nonzerodivisor

Reducing an exact finite free complex over a local ring modulo a nonzerodivisor `x` gives a
complex that is exact one degree shorter.

## Implementation details

The cycle-lifting argument from the short exact sequence of complexes is carried out directly in
coordinates, without homology objects: a reduced cycle lifts to `w` with `φ_i(w) = x t`, exactness
gives `t = φ_i(z)`, and `w - x z` is a cycle with the same reduction (`lift_reduced_cycle`). The
hypotheses that `R` is local and `x ∈ maximalIdeal R` follow the source but are not used.

## References

* [Stacks, Tag 00MZ]
-/

@[expose] public section

universe u

private theorem lift_reduced_cycle
    {R : Type u} [CommRing R] {a b c : ℕ}
    (A : Matrix (Fin b) (Fin a) R) (B : Matrix (Fin c) (Fin b) R)
    (hAB : Function.Exact A.mulVec B.mulVec)
    (x : R) (hx : x ∈ nonZeroDivisors R)
    (v : Fin a → R ⧸ Ideal.span ({x} : Set R))
    (hv : (A.map (Ideal.Quotient.mk _)).mulVec v = 0) :
    ∃ w : Fin a → R, A.mulVec w = 0 ∧
      (fun j ↦ Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (w j)) = v := by
  classical
  let q : R →+* R ⧸ Ideal.span ({x} : Set R) := Ideal.Quotient.mk _
  obtain ⟨w, hw⟩ : ∃ w : Fin a → R, q ∘ w = v := by
    exact Function.Surjective.piMap (fun _ ↦ Ideal.Quotient.mk_surjective) v
  have hdiv : ∀ j, ∃ t : R, A.mulVec w j = x * t := by
    intro j
    have hz : q (A.mulVec w j) = 0 := by
      rw [RingHom.map_mulVec, hw, hv]
      rfl
    exact (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)).imp
      (fun t ht ↦ ht)
  choose t ht using hdiv
  have hwt : A.mulVec w = x • t := funext ht
  have hBt : B.mulVec t = 0 := by
    have hz : x • B.mulVec t = 0 := by
      rw [← Matrix.mulVec_smul, ← hwt]
      exact hAB.apply_apply_eq_zero w
    funext j
    exact (mem_nonZeroDivisors_iff.mp hx).1 _ (congrFun hz j)
  obtain ⟨z, hz⟩ := (hAB t).mp hBt
  refine ⟨w - x • z, ?_, ?_⟩
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hz, hwt, sub_self]
  · funext j
    change q (w j - x * z j) = v j
    have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self x)
    simp only [map_sub, map_mul, hqx, zero_mul, sub_zero]
    exact congrFun hw j

/-- Given an exact finite free complex over a local ring, reduction modulo a
nonzerodivisor is exact one degree shorter.
-/
theorem free_complex_mod_nonzerodivisor_exact
    (R : Type u) [CommRing R] [IsLocalRing R]
    (e : ℕ) (he : 2 ≤ e) (n : ℕ → ℕ)
    (φ : ∀ i : ℕ, Matrix (Fin (n (i - 1))) (Fin (n i)) R)
    (hcomplex : ∀ i : ℕ, 1 ≤ i → i < e →
      ∀ v : Fin (n (i + 1)) → R,
        (φ i).mulVec ((φ (i + 1)).mulVec v) = 0)
    (hexact : ∀ i : ℕ, 1 ≤ i → i < e →
      Function.Exact (φ (i + 1)).mulVec (φ i).mulVec)
    (hinjective : Function.Injective (φ e).mulVec)
    (x : R) (hxmem : x ∈ IsLocalRing.maximalIdeal R)
    (hx : x ∈ nonZeroDivisors R) :
    let S := R ⧸ Ideal.span ({x} : Set R)
    let q : R →+* S := Ideal.Quotient.mk _
    let φbar : ∀ i : ℕ, Matrix (Fin (n (i - 1))) (Fin (n i)) S :=
      fun i => (φ i).map q
    Function.Injective (φbar e).mulVec ∧
      (∀ i : ℕ, 2 ≤ i → i < e →
        Function.Exact (φbar (i + 1)).mulVec (φbar i).mulVec) := by
  have _ := hxmem
  dsimp
  let q : R →+* R ⧸ Ideal.span ({x} : Set R) := Ideal.Quotient.mk _
  have hlift (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ e)
      (v : Fin (n i) → R ⧸ Ideal.span ({x} : Set R))
      (hv : ((φ i).map q).mulVec v = 0) :
      ∃ w : Fin (n i) → R, (φ i).mulVec w = 0 ∧ q ∘ w = v := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact lift_reduced_cycle (φ (j + 1)) (φ j)
      (hexact j (by omega) (by omega)) x hx v hv
  constructor
  · intro v w hvw
    have hv : ((φ e).map q).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    obtain ⟨a, ha, hared⟩ := hlift e he le_rfl (v - w) hv
    have ha0 : a = 0 := hinjective (ha.trans (Matrix.mulVec_zero _).symm)
    apply sub_eq_zero.mp
    rw [← hared, ha0]
    exact funext (fun _ ↦ map_zero q)
  · intro i hi hie v
    constructor
    · intro hv
      obtain ⟨w, hw, hred⟩ := hlift i hi (by omega) v hv
      obtain ⟨a, ha⟩ := (hexact i (by omega) hie w).mp hw
      refine ⟨q ∘ a, ?_⟩
      calc
        ((φ (i + 1)).map q).mulVec (q ∘ a) = q ∘ (φ (i + 1)).mulVec a :=
          (funext (RingHom.map_mulVec q (φ (i + 1)) a)).symm
        _ = v := by rw [ha]; exact hred
    · rintro ⟨a, rfl⟩
      obtain ⟨w, rfl⟩ : ∃ w : Fin (n (i + 1)) → R, q ∘ w = a :=
        Function.Surjective.piMap (fun _ ↦ Ideal.Quotient.mk_surjective) a
      have hmap (j : ℕ) (z : Fin (n j) → R) :
          ((φ j).map q).mulVec (q ∘ z) = q ∘ (φ j).mulVec z :=
        (funext (RingHom.map_mulVec q (φ j) z)).symm
      rw [hmap, hmap, hcomplex i (by omega) hie w]
      exact funext (fun _ ↦ map_zero q)
