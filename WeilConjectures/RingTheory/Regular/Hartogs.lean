/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Gluing along a regular pair

Let `M` be a module over a commutative ring `R` and `r, s ∈ R` such that `r` and `s` are
`M`-regular and `s` is regular on `M / rM` (for instance `[r, s]` a weakly regular sequence with
`s` also `M`-regular). Then `M` is the fibre product of its localizations `M_r` and `M_s` over
`M_{rs}`: compatible elements of `M_r` and `M_s` glue to a unique element of `M`. Geometrically,
sections of `M~` over `D(r) ∪ D(s)` extend uniquely to `Spec R`; this is the elementary form of
"depth at least two along `V(r, s)`" used for Hartogs-type extension arguments.

## Main statements

- `RingTheory.Sequence.exists_eq_smul_of_pow_smul_sub`: if `(r s)^N (s^l m - r^k n) = 0` then
  `m = r^k z` and `n = s^l z` for some `z`.
- `RingTheory.Sequence.exists_eq_of_isLocalizedModule`: the gluing statement for abstract
  localizations `M → M_r`, `M → M_s`, `M → M_{rs}`.
-/

@[expose] public section

open scoped Pointwise

namespace RingTheory.Sequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r s : R}

/-- If `s` is regular on `M / rM` then so is every power of `s`. -/
lemma mem_smul_top_of_pow_smul_mem
    (hs : ∀ m : M, s • m ∈ r • (⊤ : Submodule R M) → m ∈ r • (⊤ : Submodule R M))
    (l : ℕ) {m : M} (hm : s ^ l • m ∈ r • (⊤ : Submodule R M)) :
    m ∈ r • (⊤ : Submodule R M) := by
  induction l generalizing m with
  | zero => simpa using hm
  | succ l ih => exact ih (hs _ (by rwa [pow_succ', mul_smul] at hm))

/-- If `r` is `M`-regular and `s` is regular on `M / rM`, then `s ^ l` is regular on
`M / r ^ k M`. -/
lemma mem_pow_smul_top_of_pow_smul_mem (hr : IsSMulRegular M r)
    (hs : ∀ m : M, s • m ∈ r • (⊤ : Submodule R M) → m ∈ r • (⊤ : Submodule R M))
    (k l : ℕ) {m : M} (hm : s ^ l • m ∈ (r ^ k) • (⊤ : Submodule R M)) :
    m ∈ (r ^ k) • (⊤ : Submodule R M) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    obtain ⟨n, -, hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    have h1 : s ^ l • m ∈ r • (⊤ : Submodule R M) := by
      rw [← hn, pow_succ', mul_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (mem_smul_top_of_pow_smul_mem hs l h1)
    have h2 : s ^ l • m' = r ^ k • n := by
      apply hr
      simp only [smul_comm r (s ^ l), ← hn, pow_succ', mul_smul]
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (ih (by rw [h2]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top))
    rw [← mul_smul, ← pow_succ']
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- **Gluing along a regular pair, elementwise form.** Let `r` and `s` be `M`-regular with `s`
regular on `M / rM`. If `(r s) ^ N • (s ^ l • m - r ^ k • n) = 0`, then `m = r ^ k • z` and
`n = s ^ l • z` for some `z ∈ M`. -/
lemma exists_eq_smul_of_pow_smul_sub (hr : IsSMulRegular M r) (hs' : IsSMulRegular M s)
    (hs : ∀ m : M, s • m ∈ r • (⊤ : Submodule R M) → m ∈ r • (⊤ : Submodule R M))
    {k l N : ℕ} {m n : M} (h : (r * s) ^ N • (s ^ l • m - r ^ k • n) = 0) :
    ∃ z : M, m = r ^ k • z ∧ n = s ^ l • z := by
  have h' : s ^ l • m = r ^ k • n := by
    rw [mul_pow, mul_smul] at h
    have h1 : s ^ N • (s ^ l • m - r ^ k • n) = 0 :=
      (hr.pow N) (by beta_reduce; rw [h, smul_zero])
    exact sub_eq_zero.1 ((hs'.pow N) (by beta_reduce; rw [h1, smul_zero]))
  obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
    (mem_pow_smul_top_of_pow_smul_mem hr hs k l
      (by rw [h']; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top))
  refine ⟨z, rfl, (hr.pow k) ?_⟩
  simp only [← h', smul_comm (r ^ k) (s ^ l)]

/-- If `[r, s]` is weakly regular on `M`, then `r` is `M`-regular and `s` is regular on
`M / rM`, in the elementwise form used by `exists_eq_smul_of_pow_smul_sub`. -/
lemma IsWeaklyRegular.isSMulRegular_and_mem_smul_top (h : IsWeaklyRegular M [r, s]) :
    IsSMulRegular M r ∧
      ∀ m : M, s • m ∈ r • (⊤ : Submodule R M) → m ∈ r • (⊤ : Submodule R M) := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  refine ⟨h.1, fun m hm ↦ ?_⟩
  have : s • (Submodule.Quotient.mk m : QuotSMulTop r M) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hm
  have h0 : (Submodule.Quotient.mk m : QuotSMulTop r M) = 0 :=
    h.2 (by beta_reduce; rw [this, smul_zero])
  rwa [Submodule.Quotient.mk_eq_zero] at h0

variable {Mr Ms Mrs : Type*} [AddCommGroup Mr] [Module R Mr] [AddCommGroup Ms] [Module R Ms]
  [AddCommGroup Mrs] [Module R Mrs]

/-- **Gluing along a regular pair.** Let `r` and `s` be `M`-regular with `s` regular on
`M / rM`, and let `M → M_r`, `M → M_s`, `M → M_{rs}` be localizations, with compatible maps
`M_r → M_{rs}` and `M_s → M_{rs}`. Then elements of `M_r` and `M_s` with the same image in
`M_{rs}` come from an element of `M`. -/
theorem exists_eq_of_isLocalizedModule (hr : IsSMulRegular M r) (hs' : IsSMulRegular M s)
    (hs : ∀ m : M, s • m ∈ r • (⊤ : Submodule R M) → m ∈ r • (⊤ : Submodule R M))
    (fr : M →ₗ[R] Mr) [IsLocalizedModule (Submonoid.powers r) fr]
    (fs : M →ₗ[R] Ms) [IsLocalizedModule (Submonoid.powers s) fs]
    (frs : M →ₗ[R] Mrs) [IsLocalizedModule (Submonoid.powers (r * s)) frs]
    (gr : Mr →ₗ[R] Mrs) (gs : Ms →ₗ[R] Mrs) (hgr : gr ∘ₗ fr = frs) (hgs : gs ∘ₗ fs = frs)
    (x : Mr) (y : Ms) (hxy : gr x = gs y) : ∃ m : M, fr m = x ∧ fs m = y := by
  obtain ⟨⟨m, u⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers r) fr x
  obtain ⟨⟨n, v⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers s) fs y
  obtain ⟨k, hk⟩ := u.2
  dsimp only at hk
  obtain ⟨l, hl⟩ := v.2
  dsimp only at hl
  simp only [Function.uncurry_apply_pair] at hxy ⊢
  have hx : r ^ k • IsLocalizedModule.mk' fr m u = fr m := by
    rw [hk, ← Submonoid.smul_def]; exact IsLocalizedModule.mk'_cancel' fr m u
  have hy : s ^ l • IsLocalizedModule.mk' fs n v = fs n := by
    rw [hl, ← Submonoid.smul_def]; exact IsLocalizedModule.mk'_cancel' fs n v
  have heq : frs (s ^ l • m) = frs (r ^ k • n) := by
    have e1 : frs m = gr (fr m) := by rw [← hgr]; rfl
    have e2 : frs n = gs (fs n) := by rw [← hgs]; rfl
    rw [map_smul, map_smul, e1, e2, ← hx, ← hy, map_smul, map_smul, hxy, smul_comm]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (r * s)) heq
  obtain ⟨z, rfl, rfl⟩ := exists_eq_smul_of_pow_smul_sub hr hs' hs
    (k := k) (l := l) (N := N) (m := m) (n := n) (by simpa [smul_sub, sub_eq_zero, Submonoid.smul_def] using hN)
  refine ⟨z, ?_, ?_⟩
  · refine (IsLocalizedModule.mk'_eq_iff.2 ?_).symm
    rw [map_smul, Submonoid.smul_def, hk]
  · refine (IsLocalizedModule.mk'_eq_iff.2 ?_).symm
    rw [map_smul, Submonoid.smul_def, hl]

end RingTheory.Sequence
