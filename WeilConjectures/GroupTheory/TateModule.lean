/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Integral and rational Tate modules

Let `ℓ` be a prime and `M` an abelian group. Writing `M[ℓ ^ n]` for the `ℓ ^ n`-torsion of `M`,
the *(integral) Tate module* of `M` is the inverse limit

```
T_ℓ M = {(t n) ∈ ∏ n, M[ℓ ^ n] | ∀ n, ℓ • t (n + 1) = t n}
```

taken along multiplication by `ℓ`. It is realised here as an `AddSubgroup` of the product
`∀ n : ℕ, M`, cut out by the two conditions `ℓ ^ n • t n = 0` and `ℓ • t (n + 1) = t n`. It
carries a natural `ℤ_[ℓ]`-action, in which an `ℓ`-adic integer `a` acts on the `n`-th coordinate
through the integer `PadicInt.appr a n`, a representative of `a` modulo `ℓ ^ n`; the *rational
Tate module* is the `ℚ_[ℓ]`-vector space `V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`.

## Main definitions

- `AddCommGroup.tateModule`: the integral Tate module `T_ℓ M`.
- `AddCommGroup.tateModule.instModule`: its `ℤ_[ℓ]`-module structure.
- `AddCommGroup.rationalTateModule`: the rational Tate module `V_ℓ M`.
- `AddCommGroup.tateModule.map`, `AddCommGroup.rationalTateModule.map`: the maps induced by a
  homomorphism `M →+ N`.

## Main statements

- `AddCommGroup.tateModule.eq_zero_of_pow_zsmul_eq_zero`: `T_ℓ M` has no `ℓ`-power torsion; it
  is a torsion-free `ℤ_[ℓ]`-module.
- `AddCommGroup.rationalTateModule.injective_one_tmul`: `T_ℓ M → V_ℓ M` is injective.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AddCommGroup

variable (ℓ : ℕ) [Fact ℓ.Prime] (M : Type u) [AddCommGroup M]

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The *Tate module* `T_ℓ M` of an abelian group `M` at a prime `ℓ` is the subgroup of the product
`∀ n : ℕ, M` consisting of the compatible systems `t` of `ℓ ^ n`-torsion points, that is, those
`t` with `ℓ ^ n • t n = 0` for all `n` and `ℓ • t (n + 1) = t n` for all `n`. -/
def tateModule : AddSubgroup (∀ _ : ℕ, M) where
  carrier := {t | (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, (ℓ : ℤ) • t (n + 1) = t n}
  zero_mem' := by simp
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦
    ⟨fun n ↦ by simp [smul_add, ha n, hb n], fun n ↦ by simp [smul_add, ha' n, hb' n]⟩
  neg_mem' := fun ⟨ha, ha'⟩ ↦ ⟨fun n ↦ by simp [ha n], fun n ↦ by simp [ha' n]⟩

namespace tateModule

variable {ℓ M}

omit [Fact ℓ.Prime] in
theorem mem_iff {t : ∀ _ : ℕ, M} :
    t ∈ tateModule ℓ M ↔
      (∀ n, (ℓ : ℤ) ^ n • t n = 0) ∧ ∀ n, (ℓ : ℤ) • t (n + 1) = t n :=
  Iff.rfl

omit [Fact ℓ.Prime] in
/-- The `n`-th coordinate of an element of `T_ℓ M` is killed by `ℓ ^ n`. -/
theorem pow_zsmul_coe (t : tateModule ℓ M) (n : ℕ) :
    (ℓ : ℤ) ^ n • (t : ∀ _ : ℕ, M) n = 0 :=
  (mem_iff.mp t.2).1 n

omit [Fact ℓ.Prime] in
/-- The transition maps of `T_ℓ M` are multiplication by `ℓ`. -/
theorem zsmul_coe_succ (t : tateModule ℓ M) (n : ℕ) :
    (ℓ : ℤ) • (t : ∀ _ : ℕ, M) (n + 1) = (t : ∀ _ : ℕ, M) n :=
  (mem_iff.mp t.2).2 n

omit [Fact ℓ.Prime] in
/-- Two integers congruent modulo `ℓ ^ n` act in the same way on the `n`-th coordinate of an
element of the Tate module. -/
theorem zsmul_coe_congr {t : tateModule ℓ M} {n : ℕ} {x y : ℤ} (h : (ℓ : ℤ) ^ n ∣ x - y) :
    x • (t : ∀ _ : ℕ, M) n = y • (t : ∀ _ : ℕ, M) n := by
  obtain ⟨c, hc⟩ := h
  have hx : x = (ℓ : ℤ) ^ n * c + y := sub_eq_iff_eq_add.mp hc
  rw [hx, add_smul, mul_comm, mul_smul, pow_zsmul_coe, smul_zero, zero_add]

theorem natCast_appr (a : ℤ_[ℓ]) (n : ℕ) :
    ((a.appr n : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a :=
  rfl

omit [Fact ℓ.Prime] in
theorem dvd_sub_of_intCast_eq {n : ℕ} {x y : ℤ}
    (h : (x : ZMod (ℓ ^ n)) = (y : ZMod (ℓ ^ n))) : (ℓ : ℤ) ^ n ∣ x - y := by
  have h0 : ((x - y : ℤ) : ZMod (ℓ ^ n)) = 0 := by push_cast [h]; ring
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) (ℓ ^ n)).mp h0
  exact_mod_cast this

/-- An `ℓ`-adic integer acts on the `n`-th coordinate of the Tate module through any integer
representing it modulo `ℓ ^ n`. -/
theorem appr_zsmul_coe_eq (t : tateModule ℓ M) (a : ℤ_[ℓ]) {n : ℕ} {x : ℤ}
    (h : (x : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) :
    (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n = x • (t : ∀ _ : ℕ, M) n :=
  zsmul_coe_congr (dvd_sub_of_intCast_eq (by rw [Int.cast_natCast, natCast_appr, h]))

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The Tate module `T_ℓ M` is a module over the ring `ℤ_[ℓ]` of `ℓ`-adic integers, acting
coordinatewise: an `ℓ`-adic integer acts on the `n`-th coordinate through its reduction modulo
`ℓ ^ n`. -/
noncomputable instance instSMul : SMul ℤ_[ℓ] (tateModule ℓ M) where
  smul a t := ⟨fun n ↦ (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n, by
    refine ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · dsimp only
      rw [smul_comm, pow_zsmul_coe, smul_zero]
    · dsimp only
      rw [smul_comm, zsmul_coe_succ]
      refine zsmul_coe_congr ?_
      obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
      refine ⟨c, ?_⟩
      have hsub : (a.appr (n + 1) : ℤ) - (a.appr n : ℤ) = ((a.appr (n + 1) - a.appr n : ℕ) : ℤ) :=
        (Nat.cast_sub (a.appr_mono (Nat.le_succ n))).symm
      rw [hsub, hc]
      push_cast
      ring⟩

theorem coe_smul_apply (a : ℤ_[ℓ]) (t : tateModule ℓ M) (n : ℕ) :
    ((a • t : tateModule ℓ M) : ∀ _ : ℕ, M) n = (a.appr n : ℤ) • (t : ∀ _ : ℕ, M) n :=
  rfl

noncomputable instance instModule : Module ℤ_[ℓ] (tateModule ℓ M) where
  one_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 1 (x := 1) (by rw [Int.cast_one, map_one]), one_smul]
  mul_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, coe_smul_apply, coe_smul_apply,
      appr_zsmul_coe_eq t (a * b) (x := (a.appr n : ℤ) * (b.appr n : ℤ))
        (by push_cast [natCast_appr]; rw [map_mul]), mul_smul]
  smul_zero a := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply]
  smul_add a s t := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply, smul_add]
  add_smul a b t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t (a + b) (x := (a.appr n : ℤ) + (b.appr n : ℤ))
        (by push_cast [natCast_appr]; rw [map_add]), add_smul]
    simp [coe_smul_apply]
  zero_smul t := Subtype.ext <| funext fun n ↦ by
    rw [coe_smul_apply, appr_zsmul_coe_eq t 0 (x := 0) (by rw [Int.cast_zero, map_zero]), zero_smul]
    simp

omit [Fact ℓ.Prime] in
/-- The coordinates of an element of the Tate module are related by `ℓ ^ k • t (n + k) = t n`. -/
theorem pow_zsmul_coe_add (t : tateModule ℓ M) (n k : ℕ) :
    (ℓ : ℤ) ^ k • (t : ∀ _ : ℕ, M) (n + k) = (t : ∀ _ : ℕ, M) n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, smul_comm, ← add_assoc, zsmul_coe_succ, ih]

omit [Fact ℓ.Prime] in
/-- Part of blueprint `lem-tate-module-no-fixed`: the Tate module has no `ℓ`-power torsion. -/
theorem eq_zero_of_pow_zsmul_eq_zero {t : tateModule ℓ M} {k : ℕ}
    (h : (ℓ : ℤ) ^ k • t = 0) : t = 0 :=
  Subtype.ext <| funext fun n ↦ by
    rw [← pow_zsmul_coe_add t n k]
    exact congr_fun (congr_arg Subtype.val h) (n + k)

/-- Part of blueprint `lem-tate-module-no-fixed`: the Tate module is a torsion-free
`ℤ_[ℓ]`-module, since a nonzero `ℓ`-adic integer is a unit times a power of `ℓ` and the Tate
module has no `ℓ`-power torsion. -/
instance : NoZeroSMulDivisors ℤ_[ℓ] (tateModule ℓ M) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a t} h := by
    by_cases ha : a = 0
    · exact Or.inl ha
    refine Or.inr (eq_zero_of_pow_zsmul_eq_zero (k := a.valuation) ?_)
    have hspec := PadicInt.unitCoeff_spec ha
    set u := PadicInt.unitCoeff ha
    have h2 : (u : ℤ_[ℓ]) • ((ℓ : ℤ_[ℓ]) ^ a.valuation • t) = 0 := by rw [smul_smul, ← hspec, h]
    have h3 := congr_arg ((u⁻¹ : ℤ_[ℓ]ˣ) • ·) h2
    simp only [smul_zero, ← Units.smul_def, inv_smul_smul] at h3
    rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
    exact_mod_cast h3

variable {N : Type*} [AddCommGroup N]

/-- The map of Tate modules `T_ℓ M → T_ℓ N` induced by a homomorphism `M →+ N`, acting
coordinatewise. -/
noncomputable def map (f : M →+ N) : tateModule ℓ M →ₗ[ℤ_[ℓ]] tateModule ℓ N where
  toFun t := ⟨fun n ↦ f ((t : ∀ _ : ℕ, M) n), fun n ↦ by rw [← map_zsmul, pow_zsmul_coe, map_zero],
    fun n ↦ by rw [← map_zsmul, zsmul_coe_succ]⟩
  map_add' s t := Subtype.ext <| funext fun n ↦ by simp
  map_smul' a t := Subtype.ext <| funext fun n ↦ by simp [coe_smul_apply]

@[simp]
theorem coe_map_apply (f : M →+ N) (t : tateModule ℓ M) (n : ℕ) :
    ((map f t : tateModule ℓ N) : ∀ _ : ℕ, N) n = f ((t : ∀ _ : ℕ, M) n) :=
  rfl

end tateModule

/-- Blueprint `sk-d-ab-tate`: Integral and rational Tate modules.

The *rational Tate module* `V_ℓ M = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ M`. -/
def rationalTateModule : Type u :=
  ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)

namespace rationalTateModule

noncomputable instance : AddCommGroup (rationalTateModule ℓ M) :=
  inferInstanceAs (AddCommGroup (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

noncomputable instance : Module ℚ_[ℓ] (rationalTateModule ℓ M) :=
  inferInstanceAs (Module ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (tateModule ℓ M)))

/-- Part of blueprint `lem-tate-module-no-fixed`: since `T_ℓ M` is a torsion-free
`ℤ_[ℓ]`-module, the natural map `T_ℓ M → V_ℓ M = ℚ_[ℓ] ⊗ T_ℓ M`, `t ↦ 1 ⊗ t`, is injective. -/
theorem injective_one_tmul :
    Function.Injective fun t : tateModule ℓ M ↦ (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t := by
  refine (injective_iff_map_eq_zero (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (tateModule ℓ M) 1)).mpr
    fun t ht ↦ ?_
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) _).mp ht
  exact (smul_eq_zero.mp hc).resolve_left (nonZeroDivisors.ne_zero c.2)

variable {ℓ M} {N : Type*} [AddCommGroup N]

/-- The map of rational Tate modules `V_ℓ M → V_ℓ N` induced by a homomorphism `M →+ N`. -/
noncomputable def map (f : M →+ N) : rationalTateModule ℓ M →ₗ[ℚ_[ℓ]] rationalTateModule ℓ N :=
  (tateModule.map f).baseChange ℚ_[ℓ]

theorem map_tmul (f : M →+ N) (a : ℚ_[ℓ]) (t : tateModule ℓ M) :
    map f (a ⊗ₜ[ℤ_[ℓ]] t : ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule ℓ M) =
      (a ⊗ₜ[ℤ_[ℓ]] tateModule.map f t : ℚ_[ℓ] ⊗[ℤ_[ℓ]] tateModule ℓ N) :=
  rfl

end rationalTateModule

end AddCommGroup
