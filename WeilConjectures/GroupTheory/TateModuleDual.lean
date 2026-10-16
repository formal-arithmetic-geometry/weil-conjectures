/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.GroupTheory.TateModule
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-!
# The `ℤ_ℓ`-dual of a Tate module as an inverse limit

Let `ℓ` be a prime and `M` an abelian group whose `ℓ`-power torsion is `ℓ`-divisible: every
`y ∈ M[ℓⁿ]` is `ℓ • z` for some `z`. A compatible family of characters
`ψ n : M[ℓⁿ] →+ ℤ/ℓⁿ`, compatibility meaning `ψ n (ℓ • y) = ψ (n + 1) y mod ℓⁿ` for
`y ∈ M[ℓⁿ⁺¹]`, is the same thing as a `ℤ_ℓ`-linear map `T_ℓ M → ℤ_ℓ`
(`AddCommGroup.tateModule.torsionDualLimitAddEquiv`): the map `f` attached to `ψ` is
characterised by `f t ≡ ψ n (t n) mod ℓⁿ`, and conversely `ψ n y` is the reduction modulo `ℓⁿ`
of `f t` for any `t ∈ T_ℓ M` with `t n = y`. Such `t` exists by divisibility, and `f t` modulo
`ℓⁿ` only depends on `t n`: if `t n = 0`, then `t = ℓⁿ • t'` with `t' k = t (k + n)`.

No finiteness or freeness of `T_ℓ M` is needed.

## Main definitions

- `AddCommGroup.torsionDualLimit`: the compatible families of characters of the `M[ℓⁿ]`.
- `AddCommGroup.tateModule.torsionDualLimitAddEquiv`: its identification with the
  `ℤ_ℓ`-dual of `T_ℓ M`.
-/

@[expose] public section

universe u

namespace AddCommGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type u) [AddCommGroup M]

/-- The inverse limit `lim_n Hom(M[ℓⁿ], ℤ/ℓⁿ)` of the duals of the torsion subgroups, along the
maps dual to multiplication by `ℓ : M[ℓⁿ⁺¹] → M[ℓⁿ]` followed by the reduction
`ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ`: the families `ψ` with `ψ n (ℓ • y) = ψ (n + 1) y mod ℓⁿ`. -/
def torsionDualLimit :
    AddSubgroup (∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) where
  carrier := {ψ | ∀ n (y : AddSubgroup.torsionBy M ((ℓ : ℤ) ^ (n + 1))),
    ψ n ⟨(ℓ : ℤ) • (y : M), AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n)) (ψ (n + 1) y)}
  add_mem' {ψ χ} hψ hχ n y := by
    simp only [Pi.add_apply, AddMonoidHom.add_apply, hψ n y, hχ n y, map_add]
  zero_mem' n y := by simp
  neg_mem' {ψ} hψ n y := by
    simp only [Pi.neg_apply, AddMonoidHom.neg_apply, hψ n y, map_neg]

variable {ℓ M}

omit [Fact ℓ.Prime] in
lemma torsionDualLimit.apply_zsmul (ψ : torsionDualLimit ℓ M) (n : ℕ)
    (y : AddSubgroup.torsionBy M ((ℓ : ℤ) ^ (n + 1))) :
    (ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) n
        ⟨(ℓ : ℤ) • (y : M), AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))
        ((ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) (n + 1) y) :=
  ψ.2 n y

namespace tateModule

/-- The `n`-th coordinate of an element of the Tate module, as an element of `M[ℓⁿ]`. -/
def coordTorsion (t : tateModule ℓ M) (n : ℕ) : AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) :=
  ⟨(t : ∀ _ : ℕ, M) n, pow_zsmul_coe t n⟩

omit [Fact ℓ.Prime] in
@[simp]
lemma coe_coordTorsion (t : tateModule ℓ M) (n : ℕ) :
    (coordTorsion t n : M) = (t : ∀ _ : ℕ, M) n :=
  rfl

omit [Fact ℓ.Prime] in
lemma coordTorsion_add (t t' : tateModule ℓ M) (n : ℕ) :
    coordTorsion (t + t') n = coordTorsion t n + coordTorsion t' n :=
  rfl

omit [Fact ℓ.Prime] in
/-- The values `ψ n (t n)` of a compatible family of characters on the coordinates of an element
of the Tate module are compatible under reduction. -/
lemma castHom_apply_coordTorsion_succ (ψ : torsionDualLimit ℓ M) (t : tateModule ℓ M) (n : ℕ) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n 1)) (ZMod (ℓ ^ n))
        ((ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) (n + 1)
          (coordTorsion t (n + 1))) =
      (ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) n
        (coordTorsion t n) := by
  rw [← torsionDualLimit.apply_zsmul]
  exact congrArg _ (Subtype.ext (zsmul_coe_succ t n))

/-- The `ℓ`-adic integer `f t` attached to a compatible family of characters `ψ` and an element
`t` of the Tate module: its reduction modulo `ℓⁿ` is `ψ n (t n)`. -/
noncomputable def dualEval (ψ : torsionDualLimit ℓ M) (t : tateModule ℓ M) : ℤ_[ℓ] :=
  PadicInt.ofCompatible
    (fun n ↦ (ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) n
      (coordTorsion t n))
    (castHom_apply_coordTorsion_succ ψ t)

lemma toZModPow_dualEval (ψ : torsionDualLimit ℓ M) (t : tateModule ℓ M) (n : ℕ) :
    PadicInt.toZModPow n (dualEval ψ t) =
      (ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) n
        (coordTorsion t n) :=
  PadicInt.toZModPow_ofCompatible _ _ n

/-- The `ℤ_ℓ`-linear map `T_ℓ M → ℤ_ℓ` attached to a compatible family of characters. -/
noncomputable def toDual (ψ : torsionDualLimit ℓ M) : tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun := dualEval ψ
  map_add' t t' := PadicInt.ext_of_toZModPow.1 fun n ↦ by
    rw [map_add, toZModPow_dualEval, toZModPow_dualEval, toZModPow_dualEval, coordTorsion_add,
      map_add]
  map_smul' a t := PadicInt.ext_of_toZModPow.1 fun n ↦ by
    have h : coordTorsion (a • t) n = ((a.appr n : ℕ) : ℤ) • coordTorsion t n := rfl
    rw [RingHom.id_apply, smul_eq_mul, map_mul, toZModPow_dualEval, toZModPow_dualEval, h,
      map_zsmul, zsmul_eq_mul, Int.cast_natCast, natCast_appr]

lemma toDual_apply (ψ : torsionDualLimit ℓ M) (t : tateModule ℓ M) :
    toDual ψ t = dualEval ψ t :=
  rfl

omit [Fact ℓ.Prime] in
/-- **Lifting torsion points to the Tate module.** If the `ℓ`-power torsion of `M` is
`ℓ`-divisible, every `y ∈ M[ℓⁿ]` is the `n`-th coordinate of an element of `T_ℓ M`: choose
successive `ℓ`-th roots `u k` of `y`, then `t k = ℓⁿ • u k`. -/
lemma exists_coordTorsion_eq
    (hdiv : ∀ (n : ℕ) (y : M), (ℓ : ℤ) ^ n • y = 0 → ∃ z : M, (ℓ : ℤ) • z = y) (n : ℕ)
    (y : AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n)) :
    ∃ t : tateModule ℓ M, coordTorsion t n = y := by
  let u : ∀ k : ℕ, {x : M // (ℓ : ℤ) ^ (n + k) • x = 0} := fun k ↦ Nat.rec
    ⟨y, y.2⟩ (fun k uk ↦ ⟨(hdiv (n + k) uk.1 uk.2).choose, by
      rw [Nat.succ_eq_add_one, ← add_assoc, pow_succ, mul_smul,
        (hdiv (n + k) uk.1 uk.2).choose_spec, uk.2]⟩) k
  have hu (k : ℕ) : (ℓ : ℤ) • (u (k + 1)).1 = (u k).1 :=
    (hdiv (n + k) (u k).1 (u k).2).choose_spec
  have hpow (k : ℕ) : (ℓ : ℤ) ^ k • (u k).1 = y := by
    induction k with
    | zero => exact one_smul ℤ _
    | succ k ih => rw [pow_succ, mul_smul, hu, ih]
  refine ⟨⟨fun k ↦ (ℓ : ℤ) ^ n • (u k).1, fun k ↦ ?_, fun k ↦ ?_⟩, Subtype.ext (hpow n)⟩
  · rw [smul_smul, ← pow_add, add_comm]
    exact (u k).2
  · rw [smul_comm, hu]

omit [Fact ℓ.Prime] in
/-- An element of the Tate module whose `n`-th coordinate vanishes is `ℓⁿ` times an element of
the Tate module, namely of `k ↦ t (k + n)`. -/
lemma exists_eq_pow_zsmul_of_coe_eq_zero {t : tateModule ℓ M} {n : ℕ}
    (h : (t : ∀ _ : ℕ, M) n = 0) : ∃ t' : tateModule ℓ M, t = (ℓ : ℤ) ^ n • t' := by
  refine ⟨⟨fun k ↦ (t : ∀ _ : ℕ, M) (k + n), fun k ↦ ?_, fun k ↦ ?_⟩, Subtype.ext (funext
    fun k ↦ (pow_zsmul_coe_add t k n).symm)⟩
  · beta_reduce
    rw [add_comm, pow_zsmul_coe_add, h]
  · beta_reduce
    rw [add_right_comm, zsmul_coe_succ]

/-- For a `ℤ_ℓ`-linear map `f : T_ℓ M → ℤ_ℓ`, the reduction of `f t` modulo `ℓⁿ` only depends on
the `n`-th coordinate of `t`. -/
lemma toZModPow_eq_of_coordTorsion_eq (f : tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) {n : ℕ}
    {t t' : tateModule ℓ M} (h : coordTorsion t n = coordTorsion t' n) :
    PadicInt.toZModPow n (f t) = PadicInt.toZModPow n (f t') := by
  obtain ⟨s, hs⟩ := exists_eq_pow_zsmul_of_coe_eq_zero (t := t - t') (n := n)
    (by rw [AddSubgroup.coe_sub, Pi.sub_apply, ← coe_coordTorsion, h, coe_coordTorsion, sub_self])
  rw [← sub_eq_zero, ← map_sub, ← map_sub, hs, map_zsmul, map_zsmul, zsmul_eq_mul, Int.cast_pow,
    Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

variable (hdiv : ∀ (n : ℕ) (y : M), (ℓ : ℤ) ^ n • y = 0 → ∃ z : M, (ℓ : ℤ) • z = y)

include hdiv in
/-- The character of `M[ℓⁿ]` attached to a `ℤ_ℓ`-linear map `f : T_ℓ M → ℤ_ℓ`:
`y ↦ f t mod ℓⁿ` for any `t ∈ T_ℓ M` with `t n = y`. -/
noncomputable def ofDualAux (f : tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (n : ℕ) :
    AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n) where
  toFun y := PadicInt.toZModPow n (f (exists_coordTorsion_eq hdiv n y).choose)
  map_zero' := by
    rw [← map_zero (PadicInt.toZModPow n), ← map_zero f]
    exact toZModPow_eq_of_coordTorsion_eq f
      ((exists_coordTorsion_eq hdiv n 0).choose_spec.trans rfl)
  map_add' y y' := by
    rw [← map_add, ← map_add]
    refine toZModPow_eq_of_coordTorsion_eq f ?_
    rw [coordTorsion_add, (exists_coordTorsion_eq hdiv n _).choose_spec,
      (exists_coordTorsion_eq hdiv n _).choose_spec, (exists_coordTorsion_eq hdiv n _).choose_spec]

lemma ofDualAux_coordTorsion (f : tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) (n : ℕ)
    (t : tateModule ℓ M) :
    ofDualAux hdiv f n (coordTorsion t n) = PadicInt.toZModPow n (f t) :=
  toZModPow_eq_of_coordTorsion_eq f (exists_coordTorsion_eq hdiv n _).choose_spec

/-- The compatible family of characters attached to a `ℤ_ℓ`-linear map `T_ℓ M → ℤ_ℓ`. -/
noncomputable def ofDual (f : tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) : torsionDualLimit ℓ M :=
  ⟨ofDualAux hdiv f, fun n y ↦ by
    obtain ⟨t, rfl⟩ := exists_coordTorsion_eq hdiv (n + 1) y
    have h : (⟨(ℓ : ℤ) • (coordTorsion t (n + 1) : M),
        AddSubgroup.zsmul_mem_torsionBy_pow (coordTorsion t (n + 1)).2⟩ :
          AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n)) = coordTorsion t n :=
      Subtype.ext (zsmul_coe_succ t n)
    rw [h, ofDualAux_coordTorsion, ofDualAux_coordTorsion, PadicInt.castHom_toZModPow_succ]⟩

/-- **The dual of the Tate module.** If the `ℓ`-power torsion of `M` is `ℓ`-divisible, the
`ℤ_ℓ`-linear maps `T_ℓ M → ℤ_ℓ` are the compatible families of characters `M[ℓⁿ] → ℤ/ℓⁿ`:
`f` corresponds to `ψ` if and only if `f t ≡ ψ n (t n) mod ℓⁿ` for all `t` and `n`. -/
noncomputable def torsionDualLimitAddEquiv :
    torsionDualLimit ℓ M ≃+ (tateModule ℓ M →ₗ[ℤ_[ℓ]] ℤ_[ℓ]) where
  toFun := toDual
  invFun := ofDual hdiv
  left_inv ψ := by
    refine Subtype.ext (funext fun n ↦ AddMonoidHom.ext fun y ↦ ?_)
    obtain ⟨t, rfl⟩ := exists_coordTorsion_eq hdiv n y
    exact (ofDualAux_coordTorsion hdiv _ n t).trans (toZModPow_dualEval ψ t n)
  right_inv f := LinearMap.ext fun t ↦ PadicInt.ext_of_toZModPow.1 fun n ↦ by
    rw [toDual_apply, toZModPow_dualEval]
    exact ofDualAux_coordTorsion hdiv f n t
  map_add' ψ χ := LinearMap.ext fun t ↦ PadicInt.ext_of_toZModPow.1 fun n ↦ by
    rw [LinearMap.add_apply, map_add, toDual_apply, toDual_apply, toDual_apply,
      toZModPow_dualEval, toZModPow_dualEval, toZModPow_dualEval]
    rfl

/-- The characterisation of `AddCommGroup.tateModule.torsionDualLimitAddEquiv`: the reduction
modulo `ℓⁿ` of `f t` is `ψ n (t n)`. -/
lemma toZModPow_torsionDualLimitAddEquiv_apply (ψ : torsionDualLimit ℓ M) (t : tateModule ℓ M)
    (n : ℕ) :
    PadicInt.toZModPow n (torsionDualLimitAddEquiv hdiv ψ t) =
      (ψ : ∀ n : ℕ, AddSubgroup.torsionBy M ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n)) n
        (coordTorsion t n) :=
  toZModPow_dualEval ψ t n

end tateModule

end AddCommGroup
