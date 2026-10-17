/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityDiagonal
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityLocal
public import WeilConjectures.RingTheory.Etale.DepthTwo.LocalToGlobal
public import WeilConjectures.RingTheory.IntegrallyClosed.RegularPairAvoid
public import WeilConjectures.RingTheory.Smooth.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# The local step of purity for normal covers of a smooth algebra

Let `R₀` be a Noetherian integrally closed domain, `q ≠ 0` a prime of `R₀`, `B` a smooth
`R₀`-algebra, `M` a `B`-algebra in which the nonzero elements of `R₀` are invertible and `T` the
integral closure of `B` in `M`. Let `P` be a prime of `B` over `q` which is not minimal over
`qB`. If `T` is finite étale over a neighbourhood of every prime `Q ⊊ P`, then `B_P ⊗_B T` is
finite étale over `B_P` (`RingTheory.DepthTwo.etale_finite_localization_of_smooth`).

Proof. Let `O = B_P`, a Noetherian normal local domain. The kernel `𝔭` of `O → (κ(q) ⊗ B)_P` is a
prime strictly between `0` and the maximal ideal (as `P` is not minimal over `qB`), so `O` has
dimension at least two, and for `0 ≠ a ∈ q` there is `b ∉ 𝔭` with `[a, b]` regular
(`IsIntegrallyClosed.exists_isWeaklyRegular_pair_of_not_le`). The integral closure is finite étale
over `D(a)` and `D(b)` (these lie in the punctured spectrum), hence finite with `(a, b)` regular
on it (`RingTheory.DepthTwo.finite_and_isRegularPair_integralClosure`), and étale by
`RingTheory.DepthTwo.etale_of_smooth_of_diagonal`.

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace Algebra

variable {D X : Type u} [CommRing D] [CommRing X] [Algebra D X]

/-- **Finite étale algebras are local on the base** (without a rank bound). -/
theorem etale_finite_of_span_eq_top' (s : Set D) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Algebra.Etale (Localization.Away g) (Localization.Away g ⊗[D] X) ∧
      Module.Finite (Localization.Away g) (Localization.Away g ⊗[D] X)) :
    Algebra.Etale D X ∧ Module.Finite D X := by
  refine ⟨RingHom.etale_algebraMap.mp (RingHom.Etale.ofLocalizationSpan (algebraMap D X) s hs
      fun g ↦ etale_awayMap_of_etale_tensor g.1 (H g.1 g.2).1), ?_⟩
  exact Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun g ↦ Localization.Away g.1) (Mₚ := fun g ↦ Localization.Away g.1 ⊗[D] X)
    (fun g ↦ TensorProduct.mk D _ X 1) fun g ↦ (H g.1 g.2).2

/-- **Finite étale base changes, locally** (without a rank bound). If elements `h` of `B` with
`B_h ⊗_B T₀` finite étale over `B_h` cover `Spec D` (through `B → D`), then `D ⊗_B T₀` is finite
étale over `D`. -/
theorem etale_finite_tensor_of_forall_isPrime' {B D T₀ : Type u} [CommRing B] [CommRing D]
    [CommRing T₀] [Algebra B D] [Algebra B T₀]
    (H : ∀ Q : Ideal D, Q.IsPrime → ∃ h : B, algebraMap B D h ∉ Q ∧
      Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀)) :
    Algebra.Etale D (D ⊗[B] T₀) ∧ Module.Finite D (D ⊗[B] T₀) := by
  let s : Set D := {g | ∃ h : B, g = algebraMap B D h ∧
    Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] T₀) ∧
    Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] T₀)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hQ, hE⟩ := H m hm.isPrime
    exact hQ (hle (Ideal.subset_span ⟨h, rfl, hE⟩))
  refine etale_finite_of_span_eq_top' s hs ?_
  rintro _ ⟨h, rfl, hE, hF⟩
  let Bh := Localization.Away h
  let Dg := Localization.Away (algebraMap B D h)
  let : Algebra Bh Dg := (Localization.awayMap (algebraMap B D) h).toAlgebra
  have : IsScalarTower B Bh Dg := IsScalarTower.of_algebraMap_eq fun b ↦ by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, IsScalarTower.algebraMap_apply B D Dg]
  let e : Dg ⊗[Bh] (Bh ⊗[B] T₀) ≃ₐ[Dg] Dg ⊗[D] (D ⊗[B] T₀) :=
    (Algebra.TensorProduct.cancelBaseChange B Bh Dg Dg T₀).trans
      (Algebra.TensorProduct.cancelBaseChange B D Dg Dg T₀).symm
  exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩

end Algebra

namespace RingTheory.DepthTwo

variable {R₀ B M : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing M] [Algebra B M] [Algebra R₀ M] [IsScalarTower R₀ B M]

/-- **The local step of purity for normal covers of a smooth algebra.** See the module
docstring. -/
theorem etale_finite_localization_of_smooth (q : Ideal R₀) [q.IsPrime] (hq : q ≠ ⊥)
    (hunit : ∀ r : R₀, r ≠ 0 → IsUnit (algebraMap R₀ M r)) (P : Ideal B) [P.IsPrime]
    (hP : q = P.comap (algebraMap R₀ B)) (hmin : P ∉ (q.map (algebraMap R₀ B)).minimalPrimes)
    (H : ∀ Q : Ideal B, Q.IsPrime → Q < P →
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M)) :
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] integralClosure B M) ∧
      Module.Finite (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] integralClosure B M) := by
  classical
  let O := Localization.AtPrime P
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ B
  obtain ⟨hOd, hOi⟩ := Algebra.Smooth.isDomain_and_isIntegrallyClosed_localization R₀ B P
  have : IsNoetherianRing O := IsLocalization.isNoetherianRing P.primeCompl O inferInstance
  set T := integralClosure B M
  let M₁ := O ⊗[B] M
  let e₀ : O ⊗[B] T ≃ₐ[O] integralClosure O M₁ :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B O M)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization P.primeCompl)
  -- `T` is finite étale over `D(c)` for `c` in the maximal ideal
  have hD (c : O) (hc : c ∈ maximalIdeal O) :
      Algebra.Etale (Localization.Away c) (Localization.Away c ⊗[O] integralClosure O M₁) ∧
        Module.Finite (Localization.Away c) (Localization.Away c ⊗[O] integralClosure O M₁) := by
    let D := Localization.Away c
    obtain ⟨hE, hF⟩ := Algebra.etale_finite_tensor_of_forall_isPrime' (B := B) (D := D)
      (T₀ := T) fun Q hQ ↦ by
        set Q' := Q.comap (algebraMap B D)
        have hQ₀ : Q.comap (algebraMap O D) ≤ maximalIdeal O :=
          IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime (algebraMap O D) Q).ne_top
        have hQ'P : Q' ≤ P := by
          have h2 := Ideal.comap_mono (f := algebraMap B O) hQ₀
          have h3 : (maximalIdeal O).comap (algebraMap B O) = P :=
            Localization.AtPrime.under_maximalIdeal (I := P)
          rwa [h3, Ideal.comap_comap,
            ← IsScalarTower.algebraMap_eq] at h2
        have hQ'ne : Q' ≠ P := by
          intro heq
          have hle : maximalIdeal O ≤ Q.comap (algebraMap O D) := by
            rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap,
              Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
            exact heq.symm.le
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ (hle hc)
            (IsLocalization.Away.algebraMap_isUnit c))
        obtain ⟨h, hh, hrest⟩ := H Q' (Ideal.comap_isPrime _ _) (lt_of_le_of_ne hQ'P hQ'ne)
        exact ⟨h, hh, hrest⟩
    let e : D ⊗[O] integralClosure O M₁ ≃ₐ[D] D ⊗[B] T :=
      (Algebra.TensorProduct.congr AlgEquiv.refl e₀.symm).trans
        (Algebra.TensorProduct.cancelBaseChange B O D D T)
    exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩
  -- the prime `𝔭` of `O` cut out by the fibre over `q`
  let 𝔭 := RingHom.ker (fiberLocalRingHom q P hP)
  have : 𝔭.IsPrime := RingHom.ker_isPrime _
  have h𝔭 : ¬ maximalIdeal O ≤ 𝔭 := by
    intro hle
    apply hmin
    refine ⟨⟨inferInstance, ?_⟩, fun Q hQ hQP x hx ↦ ?_⟩
    · rw [Ideal.map_le_iff_le_comap, hP]
    · have := hQ.1
      refine mem_of_fiberLocalRingHom_eq_zero q P hP Q hQ.2 hQP (hle ?_)
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
  -- a nonzero element `a` of `q`
  obtain ⟨a₀, ha₀q, ha₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  have : Module.Flat R₀ O := Module.Flat.trans R₀ B O
  have ha0 : algebraMap R₀ O a₀ ≠ 0 := by
    intro h0
    have hreg : IsSMulRegular O a₀ :=
      Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero ha₀)
    refine one_ne_zero (hreg (?_ : a₀ • (1 : O) = a₀ • 0))
    rw [smul_zero, Algebra.smul_def, mul_one, h0]
  have haB : algebraMap R₀ B a₀ ∈ P := by
    rw [hP] at ha₀q
    exact ha₀q
  have ham : algebraMap R₀ O a₀ ∈ maximalIdeal O := by
    rw [IsScalarTower.algebraMap_apply R₀ B O]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff O P _).2 haB
  have ha𝔭 : algebraMap R₀ O a₀ ∈ 𝔭 := by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R₀ B O, fiberLocalRingHom_algebraMap,
      Algebra.algebraMap_eq_smul_one (A := B) a₀, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
      Ideal.algebraMap_residueField_eq_zero.2 ha₀q, TensorProduct.zero_tmul, map_zero]
  -- `O` has dimension at least two: `0 ⊊ 𝔭 ⊊ 𝔪`
  have hdim : 2 ≤ ringKrullDim O := by
    let p₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
    let p₁ : PrimeSpectrum O := ⟨𝔭, inferInstance⟩
    let p₂ : PrimeSpectrum O := ⟨maximalIdeal O, inferInstance⟩
    have h₀₁ : p₀ < p₁ := (PrimeSpectrum.asIdeal_lt_asIdeal p₀ p₁).1 <|
      lt_of_le_of_ne bot_le fun h ↦ ha0 (by
        have : algebraMap R₀ O a₀ ∈ (⊥ : Ideal O) := (SetLike.ext_iff.1 h _).2 ha𝔭
        exact (Submodule.mem_bot O).1 this)
    have h₁₂ : p₁ < p₂ := (PrimeSpectrum.asIdeal_lt_asIdeal p₁ p₂).1 <|
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
        fun h ↦ h𝔭 h.ge
    let l : LTSeries (PrimeSpectrum O) := ⟨2, ![p₀, p₁, p₂], fun i ↦ by
      fin_cases i
      · exact h₀₁
      · exact h₁₂⟩
    exact Order.LTSeries.length_le_krullDim l
  -- the second element `b` of the regular pair
  obtain ⟨b, hbm, hb𝔭, hb0, hab⟩ :=
    IsIntegrallyClosed.exists_isWeaklyRegular_pair_of_not_le hdim ham ha0 𝔭 h𝔭
  -- `a` is invertible in `M₁`
  have haM : IsUnit (algebraMap O M₁ (algebraMap R₀ O a₀)) := by
    rw [IsScalarTower.algebraMap_apply R₀ B O, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (algebraMap R₀ B a₀), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
    exact (hunit a₀ ha₀).map (Algebra.TensorProduct.includeRight : M →ₐ[B] M₁)
  obtain ⟨hEa, hFa⟩ := hD _ ham
  obtain ⟨hEb, hFb⟩ := hD b hbm
  obtain ⟨hfin, hreg⟩ := finite_and_isRegularPair_integralClosure (M := M₁) hab hb0 haM
  have hE : Algebra.Etale O (integralClosure O M₁) :=
    etale_of_smooth_of_diagonal q P hP (a := a₀) hreg hb𝔭
  exact ⟨.of_equiv e₀.symm, .equiv e₀.symm.toLinearEquiv⟩

end RingTheory.DepthTwo
