/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Criteria for invertibility of modules

## Main results

- `Ideal.invertible_of_forall_isMaximal`: an ideal `I` of a domain `A` which is locally principal,
  in the sense that for every maximal ideal `𝔮` there are `0 ≠ a ∈ I` and `s ∉ 𝔮` with
  `s • I ⊆ (a)`, is an invertible `A`-module.
- `Module.Invertible.of_isLocalized_span`: a finitely presented module whose localizations away
  from a family of elements generating the unit ideal are invertible is invertible.
-/

@[expose] public section

/-- Let `I` be an ideal of a domain `A` which is locally principal: for every maximal ideal `𝔮`
there are `0 ≠ a ∈ I` and `s ∉ 𝔮` such that `a ∣ s * b` for all `b ∈ I`. Then `I` is an invertible
`A`-module. Indeed, viewing `I` as a submodule of the fraction field, `I * (1 / I) = 1` since
`s = a * (s / a)` lies in `I * (1 / I)`. -/
theorem Ideal.invertible_of_forall_isMaximal {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A)
    (h : ∀ 𝔮 : Ideal A, 𝔮.IsMaximal → ∃ a ∈ I, a ≠ 0 ∧ ∃ s ∉ 𝔮, ∀ b ∈ I, a ∣ s * b) :
    Module.Invertible A I := by
  let K := FractionRing A
  have inj := IsFractionRing.injective A K
  let I' : Submodule A K := Submodule.map (Algebra.linearMap A K) I
  have hle : I' * (1 / I') ≤ 1 := by
    rw [mul_comm, ← Submodule.le_div_iff_mul_le]
  have hge : 1 ≤ I' * (1 / I') := by
    rw [Submodule.one_le]
    let L : Ideal A := (I' * (1 / I')).comap (Algebra.linearMap A K)
    suffices L = ⊤ by
      have h1 : (1 : A) ∈ L := this ▸ Submodule.mem_top
      simpa [L] using h1
    by_contra hL
    obtain ⟨𝔮, h𝔮, hL𝔮⟩ := Ideal.exists_le_maximal L hL
    obtain ⟨a, haI, ha0, s, hs𝔮, hs⟩ := h 𝔮 h𝔮
    have ha0' : algebraMap A K a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap A K)]
      exact inj.ne ha0
    refine hs𝔮 (hL𝔮 ?_)
    have hk : algebraMap A K s / algebraMap A K a ∈ 1 / I' := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hs b hb
      rw [Submodule.mem_one]
      refine ⟨c, ?_⟩
      rw [Algebra.linearMap_apply, div_mul_eq_mul_div, ← map_mul, hc, map_mul,
        mul_div_cancel_left₀ _ ha0']
    have := Submodule.mul_mem_mul (Submodule.mem_map_of_mem (f := Algebra.linearMap A K) haI) hk
    rwa [Algebra.linearMap_apply, mul_div_cancel₀ _ ha0'] at this
  have hu : IsUnit I' := .of_mul_eq_one (1 / I') (le_antisymm hle hge)
  exact .congr ((LinearEquiv.ofEq _ _ hu.unit_spec).trans
    (Submodule.equivMapOfInjective _ inj I).symm)

open TensorProduct in
/-- **Invertibility is Zariski-local.** Let `M` be a finitely presented `R`-module and `s` a set
generating the unit ideal of `R`. If for every `r ∈ s` the localization `Mₚ r` of `M` away from
`r` is an invertible module over the localization `Rₚ r`, then `M` is invertible. Indeed the
canonical map `Mᵛ ⊗[R] M → R` localizes to the canonical map `(Mₚ r)ᵛ ⊗ Mₚ r → Rₚ r`, as dual
modules of finitely presented modules commute with localization. -/
theorem Module.Invertible.of_isLocalized_span {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (s : Set R) (hs : Ideal.span s = ⊤)
    (Rₚ : s → Type*) [∀ r, CommRing (Rₚ r)] [∀ r, Algebra R (Rₚ r)]
    [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
    (Mₚ : s → Type*) [∀ r, AddCommGroup (Mₚ r)] [∀ r, Module R (Mₚ r)]
    [∀ r, Module (Rₚ r) (Mₚ r)] [∀ r, IsScalarTower R (Rₚ r) (Mₚ r)]
    (f : ∀ r, M →ₗ[R] Mₚ r) [∀ r : s, IsLocalizedModule.Away r.1 (f r)]
    (h : ∀ r, Module.Invertible (Rₚ r) (Mₚ r)) : Module.Invertible R M := by
  let F (r : s) : Module.Dual R M ⊗[R] M →ₗ[R] Module.Dual (Rₚ r) (Mₚ r) ⊗[R] Mₚ r :=
    TensorProduct.map (IsLocalizedModule.mapExtendScalars (.powers r.1) (f r)
      (Algebra.linearMap R (Rₚ r)) (Rₚ r)) (f r)
  refine ⟨bijective_of_isLocalized_span s hs _ F Rₚ (fun r ↦ Algebra.linearMap R (Rₚ r))
    (contractLeft R M) fun r ↦ ?_⟩
  let e := IsLocalization.moduleTensorEquiv (.powers r.1) (Rₚ r) (Module.Dual (Rₚ r) (Mₚ r))
    (Mₚ r)
  have key : IsLocalizedModule.map (.powers r.1) (F r) (Algebra.linearMap R (Rₚ r))
      (contractLeft R M) =
        (contractLeft (Rₚ r) (Mₚ r)).restrictScalars R ∘ₗ
          (e.symm.restrictScalars R).toLinearMap := by
    refine IsLocalizedModule.ext (.powers r.1) (F r)
      (IsLocalizedModule.map_units (Algebra.linearMap R (Rₚ r))) ?_
    rw [IsLocalizedModule.map_comp]
    ext d m
    simp [F, e, IsLocalization.moduleTensorEquiv, TensorProduct.equivOfCompatibleSMul]
  rw [key]
  exact (h r).bijective.comp e.symm.bijective
