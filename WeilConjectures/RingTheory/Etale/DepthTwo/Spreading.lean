/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.IntegralClosureSpreading

/-!
# Spreading out étaleness of an integral closure from a local ring

Let `R` be an integrally closed domain, `B` a smooth Noetherian `R`-algebra, `B_K` its
localization at the nonzero elements of `R` and `L` a finite `B_K`-algebra. If the integral
closure of the local ring `B_P` in `B_P ⊗_B L` is finite étale over `B_P` for a prime `P` of `B`,
then there is `g ∉ P` such that the integral closure of `B_g` in `L_g` is étale over `B_g`
(`Algebra.exists_etale_integralClosure_of_etale_localization`). This is used in the depth-two
step of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]).
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable {R B Bk L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing B] [Algebra R B] [Algebra.Smooth R B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]

include Bk in
/-- If `L₀ ⊆ L` is a finite `B`-subalgebra with `L = L₀[1/R⁰]` and `L₀[1/g]` étale over `B`, then
the integral closure of `B' = B[1/g]` in `L' = L[1/g]` is `L₀[1/g]`, which is étale over `B'`. -/
theorem etale_integralClosure_of_subalgebra_away (L₀ : Subalgebra B L) [Module.Finite B L₀]
    (hL₀ : ∀ l : L, ∃ a ∈ nonZeroDivisors R, algebraMap B L (algebraMap R B a) * l ∈ L₀) (g : B)
    [Algebra.Etale B (Localization.Away (algebraMap B L₀ g))]
    (B' L' : Type*) [CommRing B'] [CommRing L'] [Algebra B B'] [IsLocalization.Away g B']
    [Algebra L L'] [IsLocalization.Away (algebraMap B L g) L'] [Algebra B' L'] [Algebra B L']
    [IsScalarTower B B' L'] [IsScalarTower B L L'] :
    Algebra.Etale B' (integralClosure B' L') := by
  set m := algebraMap B L₀ g
  let E := Localization.Away m
  have hunitL (a : R) (ha : a ∈ nonZeroDivisors R) :
      IsUnit (algebraMap B L (algebraMap R B a)) := by
    rw [IsScalarTower.algebraMap_apply B Bk L]
    exact (IsLocalization.map_units Bk
      (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : nonZeroDivisors R)⟩ :
        Algebra.algebraMapSubmonoid B (nonZeroDivisors R))).map _
  -- the injective map `φ : E → L'`
  have hsub : (Submonoid.powers m).map (L₀.val : L₀ →+* L) =
      Submonoid.powers (algebraMap B L g) := by
    rw [Submonoid.map_powers]; rfl
  have : IsLocalization ((Submonoid.powers m).map (L₀.val : L₀ →+* L)) L' := by
    rw [hsub]; infer_instance
  let φ : E →+* L' := IsLocalization.map L' (L₀.val : L₀ →+* L) (Submonoid.powers m).le_comap_map
  have hφ : Function.Injective φ :=
    IsLocalization.map_injective_of_injective (Submonoid.powers m) E L' Subtype.val_injective
  have hφmk (x : L₀) : φ (algebraMap L₀ E x) = algebraMap L L' x :=
    IsLocalization.map_eq _ _
  let : Algebra E L' := φ.toAlgebra
  -- the map `B' → E`
  have hgE : IsUnit (algebraMap B E g) := by
    rw [IsScalarTower.algebraMap_apply B L₀ E]; exact IsLocalization.Away.algebraMap_isUnit m
  let ψ : B' →+* E := IsLocalization.Away.lift g hgE
  let : Algebra B' E := ψ.toAlgebra
  have : IsScalarTower B B' E := .of_algebraMap_eq fun b ↦
    (IsLocalization.Away.lift_eq g hgE b).symm
  have : IsScalarTower B' E L' := .of_algebraMap_eq' <| IsLocalization.ringHom_ext
    (Submonoid.powers g) <| RingHom.ext fun b ↦ by
      change algebraMap B' L' (algebraMap B B' b) = φ (ψ (algebraMap B B' b))
      rw [IsLocalization.Away.lift_eq, IsScalarTower.algebraMap_apply B L₀ E, hφmk,
        ← IsScalarTower.algebraMap_apply B B' L']
      exact IsScalarTower.algebraMap_apply B L L' b
  have : Algebra.Etale B B' := .of_isLocalizationAway g
  have : Algebra.Etale B' E := .of_restrictScalars B B' E
  -- `E` is smooth over `R` and `L'` is its localization at `R⁰`
  let : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B E := .of_algebraMap_eq' rfl
  have : Algebra.Smooth R E := .comp R B E
  have hRL' (a : R) : algebraMap E L' (algebraMap R E a) =
      algebraMap L L' (algebraMap B L (algebraMap R B a)) := by
    change φ (algebraMap B E (algebraMap R B a)) = _
    rw [IsScalarTower.algebraMap_apply B L₀ E, hφmk]
    rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid E (nonZeroDivisors R)) L' := by
    refine IsLocalization.of_injective _ ?_ hφ fun l' ↦ ?_
    · rintro _ ⟨a, ha, rfl⟩
      rw [hRL']
      exact (hunitL a ha).map _
    · obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B L g)) l'
      dsimp only at hxs
      obtain ⟨k, hk⟩ := s.2
      dsimp only at hk
      obtain ⟨a, ha, hax⟩ := hL₀ x
      refine ⟨algebraMap R E a, ⟨a, ha, rfl⟩,
        IsLocalization.mk' E (⟨_, hax⟩ : L₀) (⟨m ^ k, k, rfl⟩ : Submonoid.powers m), ?_⟩
      change φ _ = _
      rw [IsLocalization.map_mk', hRL']
      rw [IsLocalization.mk'_eq_iff_eq_mul]
      change algebraMap L L' (algebraMap B L (algebraMap R B a) * x) =
        _ * algebraMap L L' ((algebraMap B L g) ^ k)
      rw [hk, mul_assoc, hxs, map_mul]
  have hbot := integralClosure_eq_bot_of_smooth_of_isLocalization (R := R) (E := E) (L := L')
  -- the integral closure of `B'` in `L'` is the image of `E`
  let S' : Subalgebra B' L' := (IsScalarTower.toAlgHom B' E L').range
  have hEq : integralClosure B' L' = S' := by
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · have hx' : IsIntegral E x := (show IsIntegral B' x from hx).tower_top
      have : x ∈ integralClosure E L' := hx'
      rw [hbot] at this
      obtain ⟨y, rfl⟩ := this
      exact ⟨y, rfl⟩
    · rintro _ ⟨e, rfl⟩
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers m) e
      obtain ⟨k, hk⟩ := s.2
      dsimp only at hk
      have hx : IsIntegral B' (algebraMap L₀ E x) :=
        ((Algebra.IsIntegral.isIntegral (R := B) x).map (IsScalarTower.toAlgHom B L₀ E)).tower_top
      have hs : IsLocalization.mk' E (1 : L₀) s = algebraMap B' E (IsLocalization.mk' B' (1 : B)
          (⟨g ^ k, pow_mem (Submonoid.mem_powers g) k⟩ : Submonoid.powers g)) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, ← hk, ← map_pow]
        change algebraMap L₀ E 1 = ψ _ * algebraMap L₀ E (algebraMap B L₀ (g ^ k))
        rw [← IsScalarTower.algebraMap_apply B L₀ E, IsScalarTower.algebraMap_apply B B' E]
        change _ = ψ _ * ψ _
        rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one, map_one]
      have hinv : IsIntegral B' (IsLocalization.mk' E (1 : L₀) s) := hs ▸ isIntegral_algebraMap
      change IsIntegral B' (IsScalarTower.toAlgHom B' E L' (IsLocalization.mk' E x s))
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact (hx.mul hinv).map (IsScalarTower.toAlgHom B' E L')
  have : Algebra.Etale B' S' :=
    .of_equiv (AlgEquiv.ofInjective (IsScalarTower.toAlgHom B' E L') hφ)
  exact .of_equiv (Subalgebra.equivOfEq _ _ hEq.symm)

variable [IsNoetherianRing B] [Module.Finite Bk L]

include R Bk in
/-- **Spreading out étaleness of the integral closure from a local ring.** If the base change
`B_P ⊗_B T₀` of the integral closure `T₀` of `B` in `L` to the local ring `B_P` is finite étale,
then there is `g ∉ P` such that the integral closure of `B' = B[1/g]` in `L' = L[1/g]` is étale
over `B'`. -/
theorem exists_etale_integralClosure_of_etale_localization (P : Ideal B) [P.IsPrime]
    (hE : Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] integralClosure B L))
    (hF : Module.Finite (Localization.AtPrime P)
      (Localization.AtPrime P ⊗[B] integralClosure B L)) :
    ∃ g ∉ P, ∀ (B' L' : Type*) [CommRing B'] [CommRing L'] [Algebra B B']
      [IsLocalization.Away g B'] [Algebra L L'] [IsLocalization.Away (algebraMap B L g) L']
      [Algebra B' L'] [Algebra B L'] [IsScalarTower B B' L'] [IsScalarTower B L L'],
      Algebra.Etale B' (integralClosure B' L') := by
  classical
  set Rp := Localization.AtPrime P
  set T₀ := integralClosure B L
  -- finitely many elements of `T₀` generate `B_P ⊗_B T₀`
  have hspan : Submodule.span Rp (Set.range fun x : T₀ ↦ (1 : Rp) ⊗ₜ[B] x) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun y ↦ ?_
    induction y with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul r t =>
      have : r ⊗ₜ[B] t = r • ((1 : Rp) ⊗ₜ[B] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  obtain ⟨s', hs'sub, hs'span⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1
    (hspan ▸ hF.fg_top)
  rw [← Set.image_univ] at hs'sub
  obtain ⟨t, -, rfl⟩ := Finset.subset_set_image_iff.1 hs'sub
  -- the finite subalgebra `L₀`
  obtain ⟨L₁, hL₁fin, hL₁⟩ := exists_finite_subalgebra_mul_mem (R := R) (B := B) (Bk := Bk) (L := L)
  let L₂ : Subalgebra B L := Algebra.adjoin B ((t : Set T₀).image Subtype.val)
  have : Module.Finite B L₂ := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((t.finite_toSet).image _) fun x hx ↦ by obtain ⟨y, -, rfl⟩ := hx; exact y.2
  let L₀ : Subalgebra B L := L₁ ⊔ L₂
  have : Module.Finite B L₀ := Subalgebra.finite_sup L₁ L₂
  have hL₀T : L₀ ≤ T₀ := sup_le (fun x hx ↦ (Algebra.IsIntegral.isIntegral (R := B)
    (⟨x, hx⟩ : L₁)).map L₁.val) (Algebra.adjoin_le (by rintro _ ⟨y, -, rfl⟩; exact y.2))
  have hL₀ (l : L) : ∃ a ∈ nonZeroDivisors R, algebraMap B L (algebraMap R B a) * l ∈ L₀ := by
    obtain ⟨a, ha, h⟩ := hL₁ l
    exact ⟨a, ha, le_sup_left (a := L₁) (b := L₂) h⟩
  -- `B_P ⊗_B L₀ ≅ B_P ⊗_B T₀`
  let ι : L₀ →ₐ[B] T₀ := Subalgebra.inclusion hL₀T
  let Φ := Algebra.TensorProduct.map (AlgHom.id Rp Rp) ι
  have hΦ : Function.Bijective Φ := by
    refine ⟨Module.Flat.lTensor_preserves_injective_linearMap (M := Rp) ι.toLinearMap
      (Subalgebra.inclusion_injective hL₀T), ?_⟩
    change Function.Surjective Φ.toLinearMap
    rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← hspan, hs'span, Submodule.span_le]
    intro y hy
    rw [Finset.coe_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx₀ : (x : L) ∈ L₀ := le_sup_right (a := L₁) (b := L₂)
      (Algebra.subset_adjoin ⟨x, hx, rfl⟩)
    exact ⟨(1 : Rp) ⊗ₜ[B] ⟨x, hx₀⟩, rfl⟩
  have : Algebra.Etale Rp (Rp ⊗[B] L₀) := .of_equiv (AlgEquiv.ofBijective Φ hΦ).symm
  -- `B_P ⊗_B L₀` is a localization of `L₀`, formally étale over `B`
  let : Algebra L₀ (Rp ⊗[B] L₀) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid L₀ P.primeCompl) (Rp ⊗[B] L₀) :=
    IsLocalization.tensorRight _ _
  have : IsScalarTower B L₀ (Rp ⊗[B] L₀) := .of_algebraMap_eq fun b ↦ by
    change algebraMap B Rp b ⊗ₜ[B] (1 : L₀) = (1 : Rp) ⊗ₜ[B] algebraMap B L₀ b
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  have : Algebra.FormallyEtale B Rp := .of_isLocalization P.primeCompl
  have : Algebra.FormallyEtale B (Rp ⊗[B] L₀) := .comp B Rp _
  have : FinitePresentation B L₀ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨_, ⟨g, hg, rfl⟩, hEt⟩ := Algebra.exists_etale_localizationAway_of_isLocalization
    (B := B) (L := Rp ⊗[B] L₀) (Algebra.algebraMapSubmonoid L₀ P.primeCompl)
  refine ⟨g, hg, fun B' L' _ _ _ _ _ _ _ _ _ _ ↦ ?_⟩
  exact etale_integralClosure_of_subalgebra_away (Bk := Bk) L₀ hL₀ g B' L'

end Algebra
