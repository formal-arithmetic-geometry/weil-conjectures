/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Abhyankar's index-one conclusion for normalized tensor factors

Source: Stacks Project, Tags 0BRM, 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-normalized-factor-index-one) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Sufficient divisibility of the base index kills tame ramification.

Source: Stacks Project, Tags 0BRM (lemma-abhyankar), 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-normalized-factor-index-one)

Proof: The field map E -> F and injective A -> F identify the two B-maps,
so B embeds in A. Since A is finite and normal, it is the normalization of B
in its fraction field. The field F is a factor of E tensor Frac(A) over
Frac(B), by inverting the nonzero elements of B. The finite normalization C
is Dedekind; at the contraction R of Q its localization is a DVR. This
contraction lies over the closed point of B. Its ramification index divides r,
which is invertible in B. Its residue degree also divides r, so its inseparable
degree (a power of the residue characteristic) is one. Thus C_R/B is tame.
The maximal-ideal power identity gives base ramification index n, divisible
by r and hence by the index at R. Apply 0BRM to C_R/B and Frac(A)/Frac(B).
Integrality transitivity and localization of integral closure (09EM) identify
the resulting local normalized tensor factor with S_Q. Its adic formal
smoothness gives ramification index one by 09E7. The length definition of
ramificationIdx agrees with this DVR index. No bound for a partially
ramified base extension is used. -/
theorem dvr_abhyankar_normalized_factor_ramificationIdx_eq_one
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (r : ℕ) (hrpos : 0 < r) (hr : IsUnit (r : B))
    (hrn : r ∣ n)
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
      Q.ramificationIdx A = 1 := by sorry

end RingTheory
