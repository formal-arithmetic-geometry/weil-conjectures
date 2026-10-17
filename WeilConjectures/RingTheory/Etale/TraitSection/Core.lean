/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.TraitSection.KummerIntegralClosure
public import WeilConjectures.RingTheory.Etale.Abhyankar
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurity

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

include Bk in
set_option maxHeartbeats 800000 in
/-- **The normalization after the tame Kummer base change is finite étale** at the section.
(Gap: purity over `A₂` and Abhyankar's lemma, see the module docstring.) -/
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
  sorry

include Bk in
set_option maxHeartbeats 800000 in
/-- **The points along the section** split the closed fibre of the normalization after the tame
Kummer base change, and are invariant under the Kummer action. (Gap: see the module
docstring.) -/
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
    ∃ ψ : Fin (Nat.card G) → (integralClosure R' (R' ⊗[R] (R ⊗[B] L)) →ₐ[R'] ResidueField R'),
      Function.Injective ψ ∧
      haveI hζR : algebraMap A R ζ ^ Nat.card G = 1 := by rw [← map_pow, hζ, map_one]
      letI := AdjoinRoot.kummerAction (Nat.card G) (algebraMap A R ϖ) hζR
      haveI : SMulCommClass (Multiplicative (ZMod (Nat.card G))) R R' :=
        AdjoinRoot.smulCommClass_kummerAction (Nat.card G) (algebraMap A R ϖ) hζR
      ∀ j (g : Multiplicative (ZMod (Nat.card G))) t,
        ψ j (Algebra.IsInvariant.integralClosureMap (R := R) (R' := R') (M := R ⊗[B] L)
          (Multiplicative (ZMod (Nat.card G))) g t) = ψ j t := by
  sorry

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
    hζ.pow_eq_one
  obtain ⟨hE, hF⟩ := RingTheory.InvariantsDescent.etale_and_finite_integralClosure_of_kummer
    n (algebraMap A R ϖ) hζR hu hn hinj hk ψ hψ hψΓ
  let e₀ : R ⊗[B] integralClosure B L ≃ₐ[R] integralClosure R M :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B R L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization P.primeCompl)
  exact ⟨.of_equiv e₀.symm, .equiv e₀.symm.toLinearEquiv⟩

end Algebra
