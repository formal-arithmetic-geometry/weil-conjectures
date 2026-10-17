/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.TraitSection.KummerIntegralClosure
public import WeilConjectures.RingTheory.Etale.TraitSection.Points
public import WeilConjectures.RingTheory.Etale.Abhyankar
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurity
public import WeilConjectures.RingTheory.Etale.TraitSection.KummerAbhyankar
public import WeilConjectures.RingTheory.Etale.TraitSection.KummerPurity

/-!
# Étaleness of the normalization at a section over a trait containing roots of unity

Let `A` be a discrete valuation ring with uniformizer `ϖ` containing a primitive `n`-th root of
unity `ζ`, `n = |G|` invertible, `B` a smooth `A`-algebra with a section `ε`, `L` a `G`-Galois
finite étale algebra over `B_K` split along the section, `P = ε⁻¹(𝔪_A)` and `R = B_P`,
`M = R ⊗_B L`. With `R' = R[t] ⧸ (tⁿ - ϖ)` and `T'` the integral closure of `R'` in `R' ⊗_R M`:

* `T'` is finite étale over `R'` (`Algebra.etale_finite_integralClosure_kummer`): by purity
  (`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`) over `A₂ = A[t] ⧸ (tⁿ - ϖ)`
  and Abhyankar's lemma (`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot`) at the
  generic points of the closed fibre;
* the closed fibre of `T'` is split by `n` distinct invariant points coming from the points
  `φ` along the section (`Algebra.exists_points_integralClosure_kummer`);

hence the integral closure of `R` in `M` is finite étale over `R`
(`RingTheory.InvariantsDescent.etale_and_finite_integralClosure_of_kummer`), which is the
statement `Algebra.etale_localization_integralClosure_of_isPrimitiveRoot`.

This is the core of the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open Polynomial IsLocalRing TensorProduct

namespace Algebra

variable {A B Bk L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]


variable (A) in
/-- The local ring `B_P` of `B` at the image `P = ε⁻¹(𝔪_A)` of the closed point under the
section `ε`. -/
noncomputable abbrev sectionLocalization (ε : B →ₐ[A] A) : Type u :=
  Localization.AtPrime ((maximalIdeal A).comap ε)

set_option maxHeartbeats 3200000 in
-- Purity and Abhyankar over `B₂ = B ⊗[A] A₂` and the comparison with `R'` are slow.
omit [IsNoetherianRing B] in
include Bk in
/-- **The normalization after the tame Kummer base change is finite étale** at the section:
by purity over `A₂` and Abhyankar's lemma, see the module docstring. -/
theorem etale_finite_integralClosure_kummer (ε : B →ₐ[A] A) (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : A)) {ϖ : A} (hϖ : Irreducible ϖ)
    [Fact (algebraMap A (sectionLocalization A ε) ϖ ∈ maximalIdeal (sectionLocalization A ε))] :
    letI R := sectionLocalization A ε
    letI R' := AdjoinRoot (X ^ Nat.card G - C (algebraMap A R ϖ))
    Algebra.Etale R' (integralClosure R' (R' ⊗[R] (R ⊗[B] L))) ∧
      Module.Finite R' (integralClosure R' (R' ⊗[R] (R ⊗[B] L))) ∧
      Module.finrank R' (integralClosure R' (R' ⊗[R] (R ⊗[B] L))) ≤ Nat.card G := by
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have : NeZero (Nat.card G) := ⟨hn0⟩
  let R := sectionLocalization A ε
  let R' := AdjoinRoot (X ^ Nat.card G - C (algebraMap A R ϖ))
  -- `A₂ = A[t] ⧸ (tⁿ - ϖ)` is a discrete valuation ring with uniformizer `t`
  let A₂ := AdjoinRoot (X ^ Nat.card G - C ϖ)
  have : IsDomain A₂ := (AdjoinRoot.isAdjoinRoot _).isDomain_of_X_pow_sub_C hϖ hn0
  have : IsDiscreteValuationRing A₂ :=
    (AdjoinRoot.isAdjoinRoot _).isDiscreteValuationRing_of_X_pow_sub_C hϖ hn0
  have hm₂ : maximalIdeal A₂ = Ideal.span {AdjoinRoot.root (X ^ Nat.card G - C ϖ)} := by
    rw [(AdjoinRoot.isAdjoinRoot _).maximalIdeal_eq_span_root hϖ hn0,
      AdjoinRoot.isAdjoinRoot_root_eq_root]
  have hroot : AdjoinRoot.root (X ^ Nat.card G - C ϖ) ^ Nat.card G = algebraMap A A₂ ϖ := by
    have h := AdjoinRoot.mk_self (f := X ^ Nat.card G - C ϖ)
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  -- `B₂ = B ⊗[A] A₂`, smooth over `A₂`
  let B₂ := B ⊗[A] A₂
  let : Algebra A₂ B₂ := Algebra.TensorProduct.rightAlgebra
  let eB : B₂ ≃ₐ[A₂] A₂ ⊗[A] B :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A B A₂).toRingEquiv) fun a ↦ rfl
  have : Algebra.Smooth A₂ B₂ := Algebra.Smooth.of_equiv eB.symm
  -- `B_K₂ = B₂ ⊗[B] B_K` is the localization of `B₂` at the nonzero elements of `A₂`
  let Bk₂ := B₂ ⊗[B] Bk
  have hinjA : Function.Injective (algebraMap A A₂) :=
    AdjoinRoot.injective_algebraMap_X_pow_sub_C (Nat.card G) ϖ
  have hR (r : A) (hr : r ∈ nonZeroDivisors A) : algebraMap A A₂ r ∈ nonZeroDivisors A₂ :=
    mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero hr
      (hinjA (h.trans (map_zero _).symm))
  have hdvd (a : A₂) (ha : a ∈ nonZeroDivisors A₂) :
      ∃ r ∈ nonZeroDivisors A, a ∣ algebraMap A A₂ r := by
    have hm : algebraMap A A₂ ϖ ∈ maximalIdeal A₂ := by
      rw [← hroot, hm₂]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Nat.pos_of_ne_zero hn0)
    obtain ⟨m, hm, hm0⟩ := IsDiscreteValuationRing.exists_dvd_algebraMap
      (fun h ↦ hϖ.ne_zero (hinjA (h.trans (map_zero _).symm))) hm (nonZeroDivisors.ne_zero ha)
    exact ⟨ϖ ^ m, mem_nonZeroDivisors_of_ne_zero fun h ↦ hm0 (by rw [h, map_zero]), hm⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid B₂ (nonZeroDivisors A₂)) Bk₂ :=
    Algebra.TraitSection.isLocalization_tensor_of_dvd hdvd hR
  -- the cover `L₂ = B₂ ⊗[B] L` of `B_K₂`
  let L₂ := Algebra.TraitSection.kummerCover A B L (Nat.card G) ϖ
  let : Algebra Bk₂ L₂ :=
    (Algebra.TraitSection.coverMap (B := B) (B₁ := B₂) (Bk := Bk) (L := L)).toRingHom.toAlgebra
  have : IsScalarTower B₂ Bk₂ L₂ := .of_algebraMap_eq fun x ↦
    ((Algebra.TraitSection.coverMap (B := B) (B₁ := B₂) (Bk := Bk) (L := L)).commutes x).symm
  obtain ⟨hE₂, hF₂, hrk₂⟩ :=
    Algebra.TraitSection.etale_finite_cover (B := B) (B₁ := B₂) (Bk := Bk) (L := L)
  have : Algebra.Etale Bk₂ L₂ := hE₂
  have : Module.Finite Bk₂ L₂ := hF₂
  -- Abhyankar's lemma at the generic points of the closed fibre, then purity
  have H (Q : Ideal B₂) [Q.IsPrime]
      (hQ : Q ∈ ((maximalIdeal A₂).map (algebraMap A₂ B₂)).minimalPrimes) :
      Algebra.Etale (Localization.AtPrime Q)
          (Localization.AtPrime Q ⊗[B₂] integralClosure B₂ L₂) ∧
        Module.Finite (Localization.AtPrime Q)
          (Localization.AtPrime Q ⊗[B₂] integralClosure B₂ L₂) := by
    rw [hm₂, Ideal.map_span, Set.image_singleton,
      Algebra.TensorProduct.right_algebraMap_apply] at hQ
    exact Algebra.TraitSection.etale_finite_localization_integralClosure_kummer (Bk := Bk) G hfix
      hrank hG hϖ Q hQ
  let := AdjoinRoot.tensorXPowSubCAlgebra (B := B) (T := R) (Nat.card G) ϖ
  have := AdjoinRoot.isScalarTower_tensorXPowSubCAlgebra (B := B) (T := R) (Nat.card G) ϖ
  have := AdjoinRoot.isLocalization_tensorXPowSubC (B := B) (T := R) (Nat.card G) ϖ
    ((maximalIdeal A).comap ε).primeCompl
  obtain ⟨hE, hF, hk⟩ := RingTheory.DepthTwo.etale_finite_tensor_integralClosure_of_minimalPrimes
    (R₀ := A₂) (B := B₂) (Bk := Bk₂) (L := L₂) (fun p ↦ (hrk₂ _ hrank p).le) H R'
  -- comparison with the integral closure of `R'`
  let e := TensorProduct.integralClosureTensorEquivOfIsLocalization (B := B) (B₂ := B₂) (T := R)
    (D := R') ((maximalIdeal A).comap ε).primeCompl L
  refine ⟨.of_equiv e, .equiv e.toLinearEquiv, ?_⟩
  have : Algebra.Smooth R' (R' ⊗[B₂] integralClosure B₂ L₂) := inferInstance
  have : Module.Flat R' (R' ⊗[B₂] integralClosure B₂ L₂) := Algebra.Smooth.flat _ _
  have : Module.Free R' (R' ⊗[B₂] integralClosure B₂ L₂) := Module.free_of_flat_of_isLocalRing
  have h := congrFun
    (Module.rankAtStalk_eq_finrank_of_free (R := R') (M := R' ⊗[B₂] integralClosure B₂ L₂))
    ⟨maximalIdeal R', inferInstance⟩
  rw [Pi.natCast_apply, Nat.cast_id] at h
  rw [← e.toLinearEquiv.finrank_eq, ← h]
  exact hk _

set_option maxHeartbeats 3200000 in
-- The comparison of the points along the section with the Kummer action is slow.
omit [Algebra.Smooth A B] [IsNoetherianRing B] [Algebra.Etale Bk L] in
include Bk in
/-- **The points along the section** split the closed fibre of the normalization after the tame
Kummer base change, and are invariant under the Kummer action
(`Algebra.TraitSection.exists_points_kummer`). -/
theorem exists_points_integralClosure_kummer (ε : B →ₐ[A] A) (G : Type*) [Group G] [Finite G]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : Fin (Nat.card G) → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap A K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) {ϖ : A} (hϖ : Irreducible ϖ) {ζ : A}
    (hζ : ζ ^ Nat.card G = 1)
    [Fact (algebraMap A (sectionLocalization A ε) ϖ ∈ maximalIdeal (sectionLocalization A ε))] :
    letI R := sectionLocalization A ε
    letI R' := AdjoinRoot (X ^ Nat.card G - C (algebraMap A R ϖ))
    letI := NeZero.of_pos (Nat.card_pos (α := G))
    Algebra.FormallyUnramified R' (integralClosure R' (R' ⊗[R] (R ⊗[B] L))) →
    Algebra.EssFiniteType R' (integralClosure R' (R' ⊗[R] (R ⊗[B] L))) →
    ∃ ψ : Fin (Nat.card G) → (integralClosure R' (R' ⊗[R] (R ⊗[B] L)) →ₐ[R'] ResidueField R'),
      Function.Injective ψ ∧
      haveI hζR : algebraMap A R ζ ^ Nat.card G = 1 := by rw [← map_pow, hζ, map_one]
      letI := AdjoinRoot.kummerAction (Nat.card G) (algebraMap A R ϖ) hζR
      haveI : SMulCommClass (Multiplicative (ZMod (Nat.card G))) R R' :=
        AdjoinRoot.smulCommClass_kummerAction (Nat.card G) (algebraMap A R ϖ) hζR
      ∀ j (g : Multiplicative (ZMod (Nat.card G))) t,
        ψ j (Algebra.IsInvariant.integralClosureMap (R := R) (R' := R') (M := R ⊗[B] L)
          (Multiplicative (ZMod (Nat.card G))) g t) = ψ j t := by
  intro hU hE
  let R := sectionLocalization A ε
  set P := (maximalIdeal A).comap ε
  have hunit (b : P.primeCompl) : IsUnit (ε.toRingHom b) := by
    by_contra h
    exact b.2 (by simpa [P, Ideal.mem_comap] using h)
  let σ₀ : R →+* A := IsLocalization.lift (M := P.primeCompl) (S := R) hunit
  have hσB (b : B) : σ₀ (algebraMap B R b) = ε b := IsLocalization.lift_eq hunit b
  let σ : R →ₐ[A] A :=
    { σ₀ with
      commutes' := fun a ↦ by
        change σ₀ (algebraMap A R a) = _
        rw [IsScalarTower.algebraMap_apply A B R, hσB]
        simp }
  let : Algebra B K := ((algebraMap A K).comp ε.toRingHom).toAlgebra
  let f₁ : R →ₐ[B] K :=
    { (algebraMap A K).comp σ.toRingHom with
      commutes' := fun b ↦ by
        change algebraMap A K (σ₀ (algebraMap B R b)) = _
        rw [hσB]
        rfl }
  let f₂ (j : Fin (Nat.card G)) : L →ₐ[B] K :=
    { φ j with commutes' := fun b ↦ congr($(hφ j) b) }
  let χ (j : Fin (Nat.card G)) : R ⊗[B] L →+* K :=
    (Algebra.TensorProduct.lift f₁ (f₂ j) fun _ _ ↦ Commute.all _ _).toRingHom
  have hχ (j : Fin (Nat.card G)) :
      (χ j).comp (algebraMap R (R ⊗[B] L)) = (algebraMap A K).comp σ.toRingHom :=
    RingHom.ext fun r ↦ by simp [χ, f₁, Algebra.TensorProduct.algebraMap_apply]
  have hχinj (j l : Fin (Nat.card G))
      (H : ∀ m : R ⊗[B] L, IsIntegral R m → χ j m = χ l m) : j = l := by
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    have hT (t : integralClosure B L) : φ j t = φ l t := by
      have hm : IsIntegral R ((1 : R) ⊗ₜ[B] (t : L)) :=
        (t.2.map (Algebra.TensorProduct.includeRight : L →ₐ[B] R ⊗[B] L)).tower_top
      simpa [χ, f₁, f₂] using H _ hm
    refine hφinj (RingHom.ext fun x ↦ ?_)
    have hx : IsIntegral Bk x := Algebra.IsIntegral.isIntegral x
    obtain ⟨⟨_, r, hr, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) x hx
    have h1 := hT ⟨_, hm⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, map_mul] at h1
    have hr0 : φ j (algebraMap B L (algebraMap A B r)) ≠ 0 := by
      rw [← RingHom.comp_apply, hφ]
      simpa using (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr)
    have hjl' : φ j (algebraMap B L (algebraMap A B r)) =
        φ l (algebraMap B L (algebraMap A B r)) := by
      have h1 := congrArg (· (algebraMap A B r)) (hφ j)
      have h2 := congrArg (· (algebraMap A B r)) (hφ l)
      simp only [RingHom.comp_apply] at h1 h2
      rw [h1, h2]
    rw [← hjl'] at h1
    exact mul_left_cancel₀ hr0 h1
  exact Algebra.TraitSection.exists_points_kummer hϖ σ χ hχ hχinj hζ

set_option synthInstance.maxHeartbeats 400000 in
-- The base change to `R'` and the Kummer descent need deep instance synthesis.
set_option maxHeartbeats 3200000 in
-- The base change to `R'` and the Kummer descent are slow to elaborate.
include Bk in
/-- **Étaleness of the normalization at a section over a trait containing the `|G|`-th roots of
unity.** See the module docstring. -/
theorem etale_localization_integralClosure_of_isPrimitiveRoot (ε : B →ₐ[A] A) (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : A))
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : Fin (Nat.card G) → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap A K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) {ζ : A} (hζ : IsPrimitiveRoot ζ (Nat.card G)) :
    Algebra.Etale (sectionLocalization A ε) (sectionLocalization A ε ⊗[B] integralClosure B L) ∧
      Module.Finite (sectionLocalization A ε)
        (sectionLocalization A ε ⊗[B] integralClosure B L) := by
  set P := (maximalIdeal A).comap ε
  let R := sectionLocalization A ε
  let n := Nat.card G
  have : NeZero n := NeZero.of_pos (Nat.card_pos (α := G))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have : Fact (algebraMap A R ϖ ∈ maximalIdeal R) := ⟨by
    rw [IsScalarTower.algebraMap_apply A B R]
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff R P _).2 ?_
    change ε (algebraMap A B ϖ) ∈ maximalIdeal A
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact hϖ.not_isUnit⟩
  have hζR : algebraMap A R ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hu (i : ℕ) (hi0 : 0 < i) (hin : i < n) : IsUnit (1 - algebraMap A R ζ ^ i) := by
    have := (hζ.isUnit_one_sub_pow hG hi0 hin).map (algebraMap A R)
    rwa [map_sub, map_one, map_pow] at this
  have hn : IsUnit (n : R) := by simpa using hG.map (algebraMap A R)
  let M := R ⊗[B] L
  have : Module.Flat B Bk :=
    IsLocalization.flat Bk (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
  have : Module.Flat B L := Module.Flat.trans B Bk L
  have : Module.Flat R M := inferInstance
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight :
      M →ₐ[R] AdjoinRoot (X ^ n - C (algebraMap A R ϖ)) ⊗[R] M) :=
    Algebra.TensorProduct.includeRight_injective
      (AdjoinRoot.injective_algebraMap_X_pow_sub_C n (algebraMap A R ϖ))
  obtain ⟨hE', hF', hk⟩ := etale_finite_integralClosure_kummer (Bk := Bk) ε G hfix hrank hG hϖ
  obtain ⟨ψ, hψ, hψΓ⟩ := exists_points_integralClosure_kummer (Bk := Bk) ε G φ hφ hφinj hϖ
    hζ.pow_eq_one ⟨hE'.formallyEtale.subsingleton_kaehlerDifferential⟩
    (@_root_.Algebra.EssFiniteType.of_finiteType _ _ _ _ _
      (@_root_.Algebra.FiniteType.of_finitePresentation _ _ _ _ _ hE'.finitePresentation))
  obtain ⟨hE, hF⟩ := RingTheory.InvariantsDescent.etale_and_finite_integralClosure_of_kummer
    n (algebraMap A R ϖ) hζR hu hn hinj hk ψ hψ hψΓ
  let e₀ : R ⊗[B] integralClosure B L ≃ₐ[R] integralClosure R M :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B R L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization P.primeCompl)
  exact ⟨.of_equiv e₀.symm, .equiv e₀.symm.toLinearEquiv⟩

end Algebra
