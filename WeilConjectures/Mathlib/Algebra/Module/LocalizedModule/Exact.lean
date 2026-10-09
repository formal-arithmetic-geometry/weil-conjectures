/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Localization commutes with kernels

## Main results

- `IsLocalizedModule.of_injective_of_exact`: given compatible left exact sequences
  `0 → K → M → N` and `0 → K' → M' → N'` in which `M → M'` and `N → N'` are localizations at `S`
  and `S` acts invertibly on `K'`, the map `K → K'` is a localization at `S`.
-/

@[expose] public section

/-- **Localization commutes with kernels.** Let `0 → K → M → N` and `K' → M' → N'` be exact
sequences of `R`-modules with `K' → M'` injective, compatible with maps `K → K'`, `M → M'`,
`N → N'`, the last two of which are localizations at `S`. If the elements of `S` act invertibly on
`K'`, then `K → K'` is a localization at `S`. -/
lemma IsLocalizedModule.of_injective_of_exact {R : Type*} [CommRing R] (S : Submonoid R)
    {K M N K' M' N' : Type*} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup K'] [AddCommGroup M'] [AddCommGroup N'] [Module R K] [Module R M] [Module R N]
    [Module R K'] [Module R M'] [Module R N'] {ι : K →ₗ[R] M} {φ : M →ₗ[R] N}
    {ι' : K' →ₗ[R] M'} {φ' : M' →ₗ[R] N'} (lK : K →ₗ[R] K') (lM : M →ₗ[R] M')
    (lN : N →ₗ[R] N') [IsLocalizedModule S lM] [IsLocalizedModule S lN]
    (hι : Function.Injective ι) (hex : Function.Exact ι φ) (hι' : Function.Injective ι')
    (hφι' : ∀ y, φ' (ι' y) = 0) (h₁ : ∀ k, lM (ι k) = ι' (lK k))
    (h₂ : ∀ m, lN (φ m) = φ' (lM m)) (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R K') s)) :
    IsLocalizedModule S lK where
  map_units := hu
  surj y := by
    obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.surj S lM (ι' y)
    dsimp only at hm
    rw [Submonoid.smul_def] at hm
    have h0 : lN (φ m) = lN 0 := by
      rw [h₂, ← hm, map_zero, map_smul, hφι', smul_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    rw [smul_zero, Submonoid.smul_def, ← map_smul] at hc
    obtain ⟨k, hk⟩ := (hex _).mp hc
    refine ⟨⟨k, c * s⟩, hι' ?_⟩
    rw [← h₁, hk, Submonoid.smul_def, map_smul, map_smul, ← hm, smul_smul, Submonoid.coe_mul]
  exists_of_eq {k₁ k₂} h := by
    have : lM (ι k₁) = lM (ι k₂) := by rw [h₁, h₁, h]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) this
    refine ⟨c, hι ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul]
    exact hc

/-- **Localization commutes with extensions.** Let `K → M → N → 0` and `0 → K' → M' → N'` be exact
sequences of `R`-modules, compatible with maps `K → K'`, `M → M'`, `N → N'`, the first and the
last of which are localizations at `S`. If the elements of `S` act invertibly on `M'`, then
`M → M'` is a localization at `S`. -/
lemma IsLocalizedModule.of_exact_of_surjective {R : Type*} [CommRing R] (S : Submonoid R)
    {K M N K' M' N' : Type*} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup K'] [AddCommGroup M'] [AddCommGroup N'] [Module R K] [Module R M] [Module R N]
    [Module R K'] [Module R M'] [Module R N'] {ι : K →ₗ[R] M} {φ : M →ₗ[R] N}
    {ι' : K' →ₗ[R] M'} {φ' : M' →ₗ[R] N'} (lK : K →ₗ[R] K') (lM : M →ₗ[R] M')
    (lN : N →ₗ[R] N') [IsLocalizedModule S lK] [IsLocalizedModule S lN]
    (hex : Function.Exact ι φ) (hφ : Function.Surjective φ) (hι' : Function.Injective ι')
    (hex' : Function.Exact ι' φ') (h₁ : ∀ k, lM (ι k) = ι' (lK k))
    (h₂ : ∀ m, lN (φ m) = φ' (lM m)) (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R M') s)) :
    IsLocalizedModule S lM where
  map_units := hu
  surj y := by
    obtain ⟨⟨n, s⟩, hn⟩ := IsLocalizedModule.surj S lN (φ' y)
    dsimp only at hn
    obtain ⟨m, rfl⟩ := hφ n
    rw [h₂, Submonoid.smul_def, ← map_smul] at hn
    obtain ⟨k', hk'⟩ := (hex' (s.1 • y - lM m)).mp (by rw [map_sub, hn, sub_self])
    obtain ⟨⟨k, t⟩, hk⟩ := IsLocalizedModule.surj S lK k'
    dsimp only at hk
    refine ⟨⟨t.1 • m + ι k, t * s⟩, ?_⟩
    change (t * s).1 • y = lM (t.1 • m + ι k)
    rw [map_add, map_smul, h₁, ← hk, Submonoid.smul_def, map_smul, hk', Submonoid.coe_mul,
      mul_smul, smul_sub, add_sub_cancel]
  exists_of_eq {m₁ m₂} h := by
    have : lN (φ (m₁ - m₂)) = 0 := by rw [h₂, map_sub, h, sub_self, map_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (this.trans (map_zero lN).symm)
    rw [smul_zero, Submonoid.smul_def, ← map_smul] at hc
    obtain ⟨k, hk⟩ := (hex _).mp hc
    have hk0 : lK k = lK 0 := by
      refine hι' ?_
      rw [← h₁, hk, map_zero, map_zero, map_smul, map_sub, h, sub_self, smul_zero]
    obtain ⟨d, hd⟩ := IsLocalizedModule.exists_of_eq (S := S) hk0
    refine ⟨d * c, ?_⟩
    rw [← sub_eq_zero, Submonoid.smul_def, Submonoid.smul_def, ← smul_sub, Submonoid.coe_mul,
      mul_smul, ← hk, ← map_smul, ← Submonoid.smul_def, hd, smul_zero, map_zero]
