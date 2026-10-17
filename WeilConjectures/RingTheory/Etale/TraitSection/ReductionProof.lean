/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.TraitSection.Core
public import WeilConjectures.RingTheory.Etale.TraitSection.Reduction

/-!
# Reduction of the trait case to a base containing the roots of unity

Let `R₀ → A₁` be a flat map to a discrete valuation ring containing a primitive `|G|`-th root of
unity, whose maximal ideal lies over `q`. Base changing the trait data to `A₁`
(`B₁ = B ⊗[R₀] A₁`, `B_K₁ = B₁ ⊗[B] B_K`, `L₁ = B₁ ⊗[B] L`) and applying
`Algebra.etale_localization_integralClosure_of_isPrimitiveRoot`, the normalization becomes finite
étale at the section after base change to `(B₁)_{P₁}`, hence is finite étale over `B_P` by
descent along the flat local map `B_P → (B₁)_{P₁}`
(`Algebra.etale_localization_integralClosure_of_baseChange`).

This is part of the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace Algebra

variable {R₀ B Bk L : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀]
  [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B] [IsNoetherianRing B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
set_option maxHeartbeats 3200000 in
include Bk in
/-- **Reduction of the trait case to a base containing the roots of unity.** See the module
docstring. -/
theorem etale_localization_integralClosure_of_baseChange (ε : B →ₐ[R₀] R₀) (q : Ideal R₀)
    [q.IsPrime] (hq0 : q ≠ ⊥) (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : R₀))
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin (Nat.card G) → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ)
    (A₁ : Type u) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra R₀ A₁]
    [Module.Flat R₀ A₁] (hinj : Function.Injective (algebraMap R₀ A₁))
    (hq₁ : (maximalIdeal A₁).comap (algebraMap R₀ A₁) = q)
    {ζ : A₁} (hζ : IsPrimitiveRoot ζ (Nat.card G))
    (hint : Function.Bijective (TensorProduct.toIntegralClosure B (B ⊗[R₀] A₁) L)) :
    Algebra.Etale (Localization.AtPrime (q.comap ε))
        (Localization.AtPrime (q.comap ε) ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.AtPrime (q.comap ε))
        (Localization.AtPrime (q.comap ε) ⊗[B] integralClosure B L) := by
  classical
  let B₁ := B ⊗[R₀] A₁
  have : Algebra.Smooth A₁ B₁ := sorry
  have : IsNoetherianRing B₁ := sorry
  have : Module.Flat B B₁ := inferInstance
  let Bk₁ := B₁ ⊗[B] Bk
  have hR (r : R₀) (hr : r ∈ nonZeroDivisors R₀) : algebraMap R₀ A₁ r ∈ nonZeroDivisors A₁ :=
    mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero hr
      (hinj (h.trans (map_zero _).symm))
  have hdvd (a : A₁) (ha : a ∈ nonZeroDivisors A₁) :
      ∃ r ∈ nonZeroDivisors R₀, a ∣ algebraMap R₀ A₁ r := by
    obtain ⟨r₀, hr₀q, hr₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hm : algebraMap R₀ A₁ r₀ ∈ maximalIdeal A₁ := by
      rw [← Ideal.mem_comap, hq₁]
      exact hr₀q
    obtain ⟨m, hm, hm0⟩ := IsDiscreteValuationRing.exists_dvd_algebraMap
      (fun h ↦ hr₀ (hinj (h.trans (map_zero _).symm))) hm (nonZeroDivisors.ne_zero ha)
    exact ⟨r₀ ^ m, mem_nonZeroDivisors_of_ne_zero fun h ↦ hm0 (by rw [h, map_zero]), hm⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors A₁)) Bk₁ :=
    Algebra.TraitSection.isLocalization_tensor_of_dvd hdvd hR
  -- the cover `L₁ = B₁ ⊗[B] L` over `Bk₁`
  let L₁ := B₁ ⊗[B] L
  let ι : Bk₁ →ₐ[B₁] L₁ := Algebra.TensorProduct.map (AlgHom.id B₁ B₁)
    (IsScalarTower.toAlgHom B Bk L)
  letI : Algebra Bk₁ L₁ := ι.toRingHom.toAlgebra
  have : IsScalarTower B₁ Bk₁ L₁ := .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : Module.Finite Bk₁ L₁ := sorry
  have : Algebra.Etale Bk₁ L₁ := sorry
  have : SMulCommClass G B L := ⟨fun g b x ↦ by
    rw [IsScalarTower.algebraMap_smul (A := Bk) b x |>.symm, smul_comm g]
    exact (IsScalarTower.algebraMap_smul (A := Bk) b (g • x))⟩
  letI := Algebra.TraitSection.rightTensorAction (B := B) (B₁ := B₁) (L := L) G
  have : SMulCommClass G Bk₁ L₁ := sorry
  have hfix₁ (x : L₁) (hx : ∀ g : G, g • x = x) : x ∈ Set.range (algebraMap Bk₁ L₁) :=
    Algebra.TraitSection.mem_range_of_forall_smul_eq (Bk := Bk) G hfix x hx
  have hrank₁ (p) : Module.rankAtStalk (R := Bk₁) L₁ p = Nat.card G := sorry
  have hG₁ : IsUnit (Nat.card G : A₁) := by simpa using hG.map (algebraMap R₀ A₁)
  -- the section
  let ε₁ : B₁ →ₐ[A₁] A₁ :=
    { Algebra.TensorProduct.lift ((IsScalarTower.toAlgHom R₀ R₀ A₁).comp ε) (AlgHom.id R₀ A₁)
        fun _ _ ↦ Commute.all _ _ with
      commutes' := fun a ↦ (Algebra.TensorProduct.lift_tmul _ _ _ (1 : B) a).trans (by simp) }
  sorry

end Algebra
