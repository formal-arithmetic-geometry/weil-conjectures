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

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.RingTheory.DvrTameTensorFactorRamificationBound

/-! # A local consequence of tame DVR base change

After base change of a tame finite separable extension along a finite extension `B ⟶ A` of
discrete valuation rings whose ramification index is divisible by the tame degrees, the local
rings of the normalized field factors over `𝔪_A` are unramified over `A`
(`RingTheory.dvr_tame_tensor_factor_map_maximalIdeal`).

## Implementation details

The proof applies Abhyankar's lemma to the localizations of the normalization of `B` in `E` and
uses only the index-one part of the conclusion.

## References

* Stacks Project, Tags 032L, 0BRM and 09E7.
-/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Maximal ideal equality after tame DVR base change. Let `B ⟶ A` be a finite faithful extension
of discrete valuation rings with `𝔪_B A = 𝔪_A^n`, `n` a unit in `B`, and `E` a finite separable
extension of `Frac B` such that every prime of the normalization `C` of `B` in `E` over `𝔪_B` has
ramification index and residue degree dividing `n`. If `F = (E ⊗_B A)/P` is a field factor and the
normalization `S` of `A` in `F` is finite over `A`, then for every prime `Q` of `S` over `𝔪_A` the
maximal ideal of `A` generates the maximal ideal of `S_Q`. -/
theorem dvr_tame_tensor_factor_map_maximalIdeal
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (hn : IsUnit (n : B))
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    (∀ (R : Ideal C) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
        R.ramificationIdx B ∣ n ∧ R.inertiaDeg B ∣ n) →
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    let := hQ
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
      (IsLocalRing.maximalIdeal A).map (algebraMap A (Localization.AtPrime Q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  have : IsScalarTower B (FractionRing B) E := .of_algebraMap_eq' rfl
  have : FiniteDimensional (FractionRing B) E := hE.1
  have : Algebra.IsSeparable (FractionRing B) E := hE.2
  have hC : Module.Finite B (integralClosure B E) :=
    IsIntegralClosure.finite B (FractionRing B) E (integralClosure B E)
  intro hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  let beta : E →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeLeft : E →ₐ[B] E ⊗[B] A).toRingHom
  have hcomp : alpha.comp (algebraMap B A) = beta.comp (algebraMap B E) := by
    ext b
    exact congrArg (Ideal.Quotient.mk P)
      (DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := B) (A := E) (B := A)) b).symm
  have hinj : Function.Injective alpha := by
    apply (RingHom.injective_iff_ker_eq_bot alpha).mpr
    apply Ideal.eq_bot_of_under_eq_bot (R := B)
    rw [Ideal.under_def, RingHom.comap_ker, hcomp]
    apply (RingHom.injective_iff_ker_eq_bot _).mp
    exact beta.injective.comp ((algebraMap (FractionRing B) E).injective.comp
      (IsFractionRing.injective B (FractionRing B)))
  intro hfinite Q hQ
  let := hQ
  intro hclosed
  have : Module.Finite A (integralClosure A F) := hfinite
  have hle := dvr_tame_tensor_factor_ramificationIdx_le B n hnpos n hnpos hn A
    hindex E hE hC hbounds P hP hinj hfinite Q hQ hclosed
  have hone : Q.ramificationIdx A = 1 := by
    have : IsNoetherianRing (integralClosure A F) :=
      IsNoetherianRing.of_finite A (integralClosure A F)
    have hpos := Ideal.ramificationIdx_pos A Q
    simp only [Nat.gcd_self, Nat.div_self hnpos] at hle
    omega
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hone
  simpa only [Ideal.under_def, hclosed] using hone


end RingTheory
