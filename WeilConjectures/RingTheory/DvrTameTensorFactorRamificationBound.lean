/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.RingTheory.DvrAbhyankarNormalizedFactor
import WeilConjectures.RingTheory.DvrNormalizedTensorFactorLift
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra

/-! # A numerical bound for tame DVR tensor factors

The ramification index over `A` of a normalized field factor of `E ⊗_B A` is at most
`r / gcd(r, n)`, where `r` bounds the tame ramification of `E / Frac B` and `n` is the
ramification index of `A` over `B` (`RingTheory.dvr_tame_tensor_factor_ramificationIdx_le`).

## Implementation details

With `t = r / gcd(r, n)`, one adjoins a `t`-th root of a uniformizer of `A` to obtain `A'` with
index `lcm(r, n)` over `B`; Abhyankar's lemma makes a local ring `T` above `Q` unramified over
`A'`, and multiplicativity of indices in `A ⟶ A' ⟶ T` and `A ⟶ S_Q ⟶ T` gives `e(S_Q/A) ∣ t`.

## References

* Stacks Project, Tags 0BRM, 09EV, 09EM, 09E7 and 032L.
-/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Quantitative tame ramification bound for a normalized tensor factor. Let `B ⟶ A` be a finite
extension of discrete valuation rings with `𝔪_B A = 𝔪_A^n`, and `E` a finite separable extension
of `Frac B` whose normalization `C` of `B` is finite over `B`, with every prime of `C` over `𝔪_B`
of ramification index and residue degree dividing `r`, a unit in `B`. If `F = (E ⊗_B A)/P` is a
field factor into which `A` injects and the normalization `S` of `A` in `F` is finite over `A`,
then every prime `Q` of `S` over `𝔪_A` has ramification index at most `r / gcd(r, n)`. -/

theorem dvr_tame_tensor_factor_ramificationIdx_le
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (r : ℕ) (hrpos : 0 < r) (hr : IsUnit (r : B))
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    Module.Finite B C →
    (∀ (R : Ideal C) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
        R.ramificationIdx B ∣ r ∧ R.inertiaDeg B ∣ r) →
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    Function.Injective alpha →
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    let := hQ
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
      Q.ramificationIdx A ≤ r / Nat.gcd r n := by
  classical
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro hC hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  intro hinj hS Q hQ hclosed
  let := hQ
  let : Module.Finite A (integralClosure A F) := hS
  let t := r / Nat.gcd r n
  have htpos : 0 < t := Nat.div_pos (Nat.le_of_dvd hrpos (Nat.gcd_dvd_left r n))
    (Nat.gcd_pos_of_pos_left n hrpos)
  have hrt : r ∣ n * t := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right r n
    refine ⟨k, ?_⟩
    calc
      n * t = (Nat.gcd r n * k) * t := congrArg (· * t) hk
      _ = (Nat.gcd r n * t) * k := by ring
      _ = r * k := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r n)]
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  let f := (Polynomial.X : Polynomial A) ^ t - Polynomial.C pi
  let A₁ := AdjoinRoot f
  obtain ⟨hdom, hdvr, hmax⟩ :=
    AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra A pi hpi t htpos
  let : IsDomain A₁ := hdom
  let : IsDiscreteValuationRing A₁ := hdvr
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C pi htpos.ne'
  let : Module.Finite A A₁ := hf.finite_adjoinRoot
  have hAinj : Function.Injective (algebraMap A A₁) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hf.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast htpos.ne'
  let : FaithfulSMul A A₁ := (faithfulSMul_iff_algebraMap_injective A A₁).mpr hAinj
  have hroot : AdjoinRoot.root f ^ t = algebraMap A A₁ pi := by
    simpa only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.eval₂_root f)
  have hidx₁ : (IsLocalRing.maximalIdeal A).map (algebraMap A A₁) =
      IsLocalRing.maximalIdeal A₁ ^ t := by
    rw [hpi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmax,
      Ideal.span_singleton_pow, hroot]
  let : IsScalarTower B A A₁ := inferInstance
  let : Module.Finite B A₁ := Module.Finite.trans A A₁
  have hidxB : (IsLocalRing.maximalIdeal B).map (algebraMap B A₁) =
      IsLocalRing.maximalIdeal A₁ ^ (n * t) := by
    rw [IsScalarTower.algebraMap_eq B A A₁, ← Ideal.map_map, hindex,
      Ideal.map_pow, hidx₁, ← pow_mul, Nat.mul_comm t n]
  obtain ⟨P₁, hP₁, hinj₁, hS₁, i, Q₁, hQ₁, hover, hclosed₁, hflat⟩ :=
    dvr_normalized_tensor_factor_lift B A E hE P hP hinj hS Q hQ hclosed A₁
  let := hP₁
  let F₁ := (E ⊗[B] A₁) ⧸ P₁
  let alpha₁ : A₁ →+* F₁ := (Ideal.Quotient.mk P₁).comp
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[B] E ⊗[B] A₁).toRingHom
  let := alpha₁.toAlgebra
  let : Algebra A F₁ := (alpha₁.comp (algebraMap A A₁)).toAlgebra
  let : IsScalarTower A A₁ F₁ := .of_algebraMap_eq' rfl
  let S₁ := integralClosure A₁ F₁
  let := hQ₁
  let : Module.Finite A₁ S₁ := hS₁
  let : Algebra (integralClosure A F) S₁ := i.toRingHom.toAlgebra
  let : IsScalarTower A (integralClosure A F) S₁ := .of_algHom i
  let : Module.Flat (integralClosure A F) S₁ := hflat
  let : Q₁.LiesOver Q := ⟨hover.symm⟩
  let : Q₁.LiesOver (IsLocalRing.maximalIdeal A₁) := ⟨hclosed₁.symm⟩
  have hone : Q₁.ramificationIdx A₁ = 1 :=
    dvr_abhyankar_normalized_factor_ramificationIdx_eq_one B (n * t)
      (Nat.mul_pos hnpos htpos) r hrpos hr hrt A₁ hidxB E hE
      hC hbounds P₁ hP₁ hinj₁ hS₁ Q₁ hQ₁ hclosed₁
  have he : (IsLocalRing.maximalIdeal A₁).ramificationIdx A = t := by
    let : (IsLocalRing.maximalIdeal A₁).LiesOver (IsLocalRing.maximalIdeal A) :=
      ⟨(IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
          (IsLocalRing.maximalIdeal A₁))).symm⟩
    let : IsDiscreteValuationRing (Localization.AtPrime (IsLocalRing.maximalIdeal A₁)) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A₁
        (IsDiscreteValuationRing.not_a_field A₁) _
    rw [Ideal.ramificationIdx_eq (IsLocalRing.maximalIdeal A),
      IsScalarTower.algebraMap_eq A A₁ (Localization.AtPrime (IsLocalRing.maximalIdeal A₁)),
      ← Ideal.map_map, hidx₁, Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  let : Module.IsTorsionFree A₁ F₁ :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj₁
  let : Module.IsTorsionFree A₁ S₁ := inferInstance
  let : Module.Flat A₁ S₁ := inferInstance
  have htotal : Q₁.ramificationIdx A = t := by
    rw [Ideal.ramificationIdx_tower (IsLocalRing.maximalIdeal A₁) Q₁, hone, mul_one, he]
  have hdvd : Q.ramificationIdx A ∣ t := by
    rw [← htotal]
    exact Ideal.ramificationIdx_below_dvd Q Q₁
  exact Nat.le_of_dvd htpos hdvd


end RingTheory
