/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.PGroup

/-!
# Fixed vectors of `p`-groups acting on `p`-primary abelian groups

A finite `p`-group acting additively on a nonzero finite abelian group of `p`-power torsion has a
nonzero fixed vector killed by `p` (blueprint `det-tf-transverse-corner-vanishing`, dévissage
step): the number of fixed points is congruent modulo `p` to the cardinality of the group, which
is divisible by `p`.

## Main statements

- `IsPGroup.exists_fixed_ne_zero_nsmul_eq_zero`
-/

@[expose] public section

namespace IsPGroup

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] {A : Type*} [AddCommGroup A]
  [Finite A] [DistribMulAction G A]

/-- A `p`-group acting additively on a nonzero finite abelian group in which every element is
killed by a power of `p` has a nonzero fixed vector (blueprint
`det-tf-transverse-corner-vanishing`). -/
theorem exists_fixed_ne_zero (hG : IsPGroup p G) (hA : ∀ a : A, ∃ n : ℕ, p ^ n • a = 0)
    [Nontrivial A] : ∃ a : A, a ≠ 0 ∧ ∀ g : G, g • a = a := by
  obtain ⟨b, hb⟩ := exists_ne (0 : A)
  obtain ⟨n, hn⟩ := hA b
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).1 (addOrderOf_dvd_of_nsmul_eq_zero hn)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hb (AddMonoid.addOrderOf_eq_one_iff.1 (by simpa using hm))
  have hpA : p ∣ Nat.card A :=
    (dvd_pow_self p hm0).trans (hm ▸ addOrderOf_dvd_natCard b)
  have hfix : p ∣ Nat.card (MulAction.fixedPoints G A) :=
    (Nat.modEq_zero_iff_dvd.1 ((hG.card_modEq_card_fixedPoints A).symm.trans
      (Nat.modEq_zero_iff_dvd.2 hpA)))
  have : Finite (MulAction.fixedPoints G A) := Subtype.finite
  have : Nontrivial (MulAction.fixedPoints G A) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have : Nonempty (MulAction.fixedPoints G A) := ⟨⟨0, fun g ↦ smul_zero g⟩⟩
    have := Finite.card_pos (α := MulAction.fixedPoints G A)
    exact lt_of_lt_of_le hp.out.one_lt (Nat.le_of_dvd this hfix)
  obtain ⟨⟨a, ha⟩, ha0⟩ := exists_ne (⟨0, fun g ↦ smul_zero g⟩ : MulAction.fixedPoints G A)
  exact ⟨a, fun h ↦ ha0 (Subtype.ext h), ha⟩

/-- **Fixed vectors of `p`-groups** (blueprint `det-tf-transverse-corner-vanishing`): a
`p`-group acting additively on a nonzero finite abelian group in which every element is killed
by a power of `p` has a nonzero fixed vector killed by `p`. -/
theorem exists_fixed_ne_zero_nsmul_eq_zero (hG : IsPGroup p G)
    (hA : ∀ a : A, ∃ n : ℕ, p ^ n • a = 0) [Nontrivial A] :
    ∃ a : A, a ≠ 0 ∧ p • a = 0 ∧ ∀ g : G, g • a = a := by
  classical
  obtain ⟨b, hb, hbG⟩ := hG.exists_fixed_ne_zero hA
  have hex : ∃ n : ℕ, p ^ n • b = 0 := hA b
  let n := Nat.find hex
  have hn : p ^ n • b = 0 := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero, one_smul] at hn
    exact hb hn
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨p ^ k • b, fun h ↦ Nat.find_min hex (show k < n by omega) h, ?_, fun g ↦ ?_⟩
  · rw [← mul_nsmul', ← pow_succ', ← hk, hn]
  · rw [smul_comm, hbG]

end IsPGroup
