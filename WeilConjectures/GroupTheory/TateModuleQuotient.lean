/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import WeilConjectures.GroupTheory.TateModule

/-!
# The Tate module modulo `ℓ ^ n`

Let `ℓ` be a prime and `M` an abelian group on which multiplication by `ℓ` is surjective. The
projection `T_ℓ M → M[ℓ ^ n]` to the `n`-th coordinate is surjective with kernel `ℓ ^ n T_ℓ M`,
so that it induces an isomorphism `T_ℓ M / ℓ ^ n T_ℓ M ≃ M[ℓ ^ n]`.

## Main definitions

- `AddCommGroup.tateModule.toTorsionBy`: the projection `T_ℓ M → M[ℓ ^ n]`.
- `AddCommGroup.tateModule.quotientAddEquivTorsionBy`: `T_ℓ M / ℓ ^ n T_ℓ M ≃ M[ℓ ^ n]`.

## Main statements

- `AddCommGroup.tateModule.ker_toTorsionBy`: the kernel of the projection is `ℓ ^ n T_ℓ M`.
- `AddCommGroup.tateModule.surjective_toTorsionBy`: the projection is surjective if `M` is
  `ℓ`-divisible.
-/

@[expose] public section

universe u

open scoped Pointwise

namespace AddCommGroup.tateModule

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type u} [AddCommGroup M]

variable (ℓ M) in
/-- The projection `T_ℓ M → M[ℓ ^ n]` of the Tate module to its `n`-th coordinate. -/
def toTorsionBy (n : ℕ) : tateModule ℓ M →+ AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) where
  toFun t := ⟨(t : ∀ _ : ℕ, M) n, pow_zsmul_coe t n⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fact ℓ.Prime] in
@[simp]
theorem coe_toTorsionBy_apply (n : ℕ) (t : tateModule ℓ M) :
    (toTorsionBy ℓ M n t : M) = (t : ∀ _ : ℕ, M) n :=
  rfl

/-- The multiple `(ℓ : ℤ_[ℓ]) ^ n • t` of an element of the Tate module has coordinates
`ℓ ^ n • t k`. -/
theorem coe_pow_smul_apply (n : ℕ) (t : tateModule ℓ M) (k : ℕ) :
    (((ℓ : ℤ_[ℓ]) ^ n • t : tateModule ℓ M) : ∀ _ : ℕ, M) k =
      (ℓ : ℤ) ^ n • (t : ∀ _ : ℕ, M) k := by
  have h : (ℓ : ℤ_[ℓ]) ^ n = (((ℓ : ℤ) ^ n : ℤ) : ℤ_[ℓ]) := by push_cast; rfl
  rw [h, Int.cast_smul_eq_zsmul]
  rfl

/-- The kernel of the projection `T_ℓ M → M[ℓ ^ n]` is `ℓ ^ n T_ℓ M`: if `t n = 0`, then
`t = ℓ ^ n • s` for the shifted element `s k = t (k + n)` of the Tate module. -/
theorem ker_toTorsionBy (n : ℕ) :
    (toTorsionBy ℓ M n).ker =
      ((ℓ : ℤ_[ℓ]) ^ n • (⊤ : Submodule ℤ_[ℓ] (tateModule ℓ M))).toAddSubgroup := by
  ext t
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro ht
    have ht' : (t : ∀ _ : ℕ, M) n = 0 := congrArg Subtype.val ht
    refine ⟨⟨fun k ↦ (t : ∀ _ : ℕ, M) (k + n), fun k ↦ ?_, fun k ↦ ?_⟩, Submodule.mem_top,
      Subtype.ext <| funext fun k ↦ ?_⟩
    · dsimp only
      rw [add_comm, pow_zsmul_coe_add, ht']
    · dsimp only
      rw [show k + 1 + n = k + n + 1 by omega, zsmul_coe_succ]
    · rw [coe_pow_smul_apply]
      exact pow_zsmul_coe_add t k n
  · rintro ⟨s, -, rfl⟩
    exact Subtype.ext ((coe_pow_smul_apply n s n).trans (pow_zsmul_coe s n))

omit [Fact ℓ.Prime] in
/-- If multiplication by `ℓ` is surjective on `M`, the projection `T_ℓ M → M[ℓ ^ n]` is
surjective: for `x ∈ M[ℓ ^ n]` choose `y k` with `y 0 = x` and `ℓ • y (k + 1) = y k`; then
`(ℓ ^ n • y k)_k` lies in the Tate module and has `n`-th coordinate `x`. -/
theorem surjective_toTorsionBy (hdiv : ∀ x : M, ∃ y : M, (ℓ : ℤ) • y = x) (n : ℕ) :
    Function.Surjective (toTorsionBy ℓ M n) := by
  choose d hd using hdiv
  rintro ⟨x, hx⟩
  have hx' : (ℓ : ℤ) ^ n • x = 0 := hx
  let y : ℕ → M := fun k ↦ d^[k] x
  have hy (k : ℕ) : (ℓ : ℤ) • y (k + 1) = y k := by
    simp only [y, Function.iterate_succ_apply']
    exact hd _
  have hyx (k : ℕ) : (ℓ : ℤ) ^ k • y k = x := by
    induction k with
    | zero => exact one_smul ℤ _
    | succ k ih => rw [pow_succ, mul_smul, hy, ih]
  refine ⟨⟨fun k ↦ (ℓ : ℤ) ^ n • y k, fun k ↦ ?_, fun k ↦ ?_⟩, Subtype.ext ?_⟩
  · rw [smul_comm, hyx, hx']
  · rw [smul_comm, hy]
  · exact hyx n

variable (ℓ M) in
/-- The projection `T_ℓ M → M[ℓ ^ n]` induces an isomorphism `T_ℓ M / ℓ ^ n T_ℓ M ≃ M[ℓ ^ n]`
when multiplication by `ℓ` is surjective on `M`. -/
noncomputable def quotientAddEquivTorsionBy (hdiv : ∀ x : M, ∃ y : M, (ℓ : ℤ) • y = x)
    (n : ℕ) :
    tateModule ℓ M ⧸ ((ℓ : ℤ_[ℓ]) ^ n • (⊤ : Submodule ℤ_[ℓ] (tateModule ℓ M))) ≃+
      AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_toTorsionBy n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_toTorsionBy hdiv n))

@[simp]
theorem quotientAddEquivTorsionBy_mk (hdiv : ∀ x : M, ∃ y : M, (ℓ : ℤ) • y = x) (n : ℕ)
    (t : tateModule ℓ M) :
    quotientAddEquivTorsionBy ℓ M hdiv n (Submodule.Quotient.mk t) = toTorsionBy ℓ M n t :=
  rfl

end AddCommGroup.tateModule
