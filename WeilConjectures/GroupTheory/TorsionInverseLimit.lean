/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.GroupTheory.TateModule

/-!
# Inverse limits of `ℓ`-power torsion groups as `ℤ_ℓ`-modules

Let `ℓ` be a prime and `(M n, f n : M (n + 1) →+ M n)` an inverse system of abelian groups. The
compatible families `t` with `ℓ ^ n • t n = 0` form a `ℤ_ℓ`-module
`AddCommGroup.torsionInverseLimit ℓ f`, an `ℓ`-adic integer `a` acting on the `n`-th coordinate
through the integer `PadicInt.appr a n`. This generalises `AddCommGroup.tateModule`, which is the
case of the constant system `M n = M` with `f n` multiplication by `ℓ`. When every `M n` is
killed by `ℓ ^ n`, the torsion condition is automatic and this is the inverse limit
`lim_n M n` (`AddCommGroup.torsionInverseLimit.mem_iff_of_forall_pow_zsmul_eq_zero`).

## Main definitions

- `AddCommGroup.torsionInverseLimit`: the inverse limit, as an `AddSubgroup` of `∀ n, M n`.
- `AddCommGroup.torsionInverseLimit.instModule`: its `ℤ_ℓ`-module structure.
-/

@[expose] public section

namespace AddCommGroup

variable (ℓ : ℕ) {M : ℕ → Type*} [∀ n, AddCommGroup (M n)] (f : ∀ n, M (n + 1) →+ M n)

/-- The inverse limit of the system `f n : M (n + 1) →+ M n` of `ℓ`-power torsion groups: the
families `t` with `ℓ ^ n • t n = 0` and `f n (t (n + 1)) = t n` for all `n`. -/
def torsionInverseLimit : AddSubgroup (∀ n, M n) where
  carrier := {t | (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, f n (t (n + 1)) = t n}
  zero_mem' := by simp
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦
    ⟨fun n ↦ by simp [smul_add, ha n, hb n], fun n ↦ by simp [ha' n, hb' n]⟩
  neg_mem' := fun ⟨ha, ha'⟩ ↦ ⟨fun n ↦ by simp [ha n], fun n ↦ by simp [ha' n]⟩

namespace torsionInverseLimit

variable {ℓ f}

theorem mem_iff {t : ∀ n, M n} :
    t ∈ torsionInverseLimit ℓ f ↔
      (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, f n (t (n + 1)) = t n :=
  Iff.rfl

/-- If every `M n` is killed by `ℓ ^ n`, the torsion inverse limit consists of all compatible
families: it is the inverse limit `lim_n M n`. -/
theorem mem_iff_of_forall_pow_zsmul_eq_zero (h : ∀ n (x : M n), (ℓ : ℤ) ^ n • x = 0)
    {t : ∀ n, M n} : t ∈ torsionInverseLimit ℓ f ↔ ∀ n, f n (t (n + 1)) = t n :=
  ⟨fun ht ↦ ht.2, fun ht ↦ ⟨fun n ↦ h n (t n), ht⟩⟩

theorem pow_zsmul_coe (t : torsionInverseLimit ℓ f) (n : ℕ) :
    (ℓ : ℤ) ^ n • (t : ∀ n, M n) n = 0 :=
  t.2.1 n

theorem map_coe_succ (t : torsionInverseLimit ℓ f) (n : ℕ) :
    f n ((t : ∀ n, M n) (n + 1)) = (t : ∀ n, M n) n :=
  t.2.2 n

/-- The `n`-th coordinate of an element of the torsion inverse limit is unchanged by integers
congruent modulo `ℓ ^ n`. -/
theorem zsmul_coe_congr {t : torsionInverseLimit ℓ f} {n : ℕ} {x y : ℤ}
    (h : (ℓ : ℤ) ^ n ∣ x - y) : x • (t : ∀ n, M n) n = y • (t : ∀ n, M n) n := by
  obtain ⟨c, hc⟩ := h
  have hx : x = (ℓ : ℤ) ^ n * c + y := sub_eq_iff_eq_add.mp hc
  rw [hx, add_smul, mul_comm, mul_smul, pow_zsmul_coe, smul_zero, zero_add]

variable [Fact ℓ.Prime]

/-- An `ℓ`-adic integer acts on the `n`-th coordinate through any integer representing it
modulo `ℓ ^ n`. -/
theorem appr_zsmul_coe_eq (t : torsionInverseLimit ℓ f) (a : ℤ_[ℓ]) {n : ℕ} {x : ℤ}
    (h : (x : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) :
    (a.appr n : ℤ) • (t : ∀ n, M n) n = x • (t : ∀ n, M n) n :=
  zsmul_coe_congr (tateModule.dvd_sub_of_intCast_eq
    (by rw [Int.cast_natCast, tateModule.natCast_appr, h]))

/-- The torsion inverse limit is a module over the `ℓ`-adic integers, acting coordinatewise: an
`ℓ`-adic integer acts on the `n`-th coordinate through its reduction modulo `ℓ ^ n`. -/
noncomputable instance instSMul : SMul ℤ_[ℓ] (torsionInverseLimit ℓ f) where
  smul a t := ⟨fun n ↦ (a.appr n : ℤ) • (t : ∀ n, M n) n, by
    refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · dsimp only
      rw [smul_comm, pow_zsmul_coe, smul_zero]
    · dsimp only
      rw [map_zsmul, map_coe_succ]
      refine zsmul_coe_congr ?_
      obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
      refine ⟨c, ?_⟩
      have hsub : (a.appr (n + 1) : ℤ) - (a.appr n : ℤ) =
          ((a.appr (n + 1) - a.appr n : ℕ) : ℤ) :=
        (Nat.cast_sub (a.appr_mono (Nat.le_succ n))).symm
      rw [hsub, hc]
      push_cast
      ring⟩

theorem coe_smul_apply (a : ℤ_[ℓ]) (t : torsionInverseLimit ℓ f) (n : ℕ) :
    ((a • t : torsionInverseLimit ℓ f) : ∀ n, M n) n = (a.appr n : ℤ) • (t : ∀ n, M n) n :=
  rfl

noncomputable instance instModule : Module ℤ_[ℓ] (torsionInverseLimit ℓ f) where
  one_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 1 (x := 1) (by rw [Int.cast_one, map_one]),
      one_smul]
  mul_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, coe_smul_apply, coe_smul_apply,
      appr_zsmul_coe_eq t (a * b) (x := (a.appr n : ℤ) * (b.appr n : ℤ))
        (by push_cast [tateModule.natCast_appr]; rw [map_mul]), mul_smul]
  smul_zero a := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply]
  smul_add a s t := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply, smul_add]
  add_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t (a + b) (x := (a.appr n : ℤ) + (b.appr n : ℤ))
        (by push_cast [tateModule.natCast_appr]; rw [map_add]), add_smul]
    simp [coe_smul_apply]
  zero_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 0 (x := 0) (by rw [Int.cast_zero, map_zero]),
      zero_smul]
    simp

end torsionInverseLimit

end AddCommGroup
