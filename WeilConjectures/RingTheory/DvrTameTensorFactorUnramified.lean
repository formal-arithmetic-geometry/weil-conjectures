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
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.RingTheory.DvrTameTensorFactorMaximalIdeal
import WeilConjectures.RingTheory.DvrTameTensorFactorResidueSeparable

/-! # The tame ramification step for a finite normalization

## References

* Stacks Project, Tags 0BRM, 09E7, 00UW and 02FM
-/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- A DVR base extension with sufficiently divisible index kills tame ramification: let `B → A`
be a finite extension of DVRs with `m_B A = m_A ^ n` and `n` a unit in `B`, and let `E` be a
finite separable extension of `Frac B` such that every prime of the normalization of `B` in `E`
over `m_B` has ramification index and inertia degree dividing `n`. Then for every field factor
`F = (E ⊗[B] A) ⧸ P`, with the normalization `S` of `A` in `F` finite over `A`, and every prime
`Q` of `S` over `m_A`, the map `A → S_Q` is formally unramified. -/
theorem dvr_tame_tensor_factor_formallyUnramified
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
      Algebra.FormallyUnramified A (Localization.AtPrime Q) := by
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro hbounds P hP
  let := hP
  let F := (E ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  intro hfinite Q hQ
  let := hQ
  intro hclosed
  have hmax := dvr_tame_tensor_factor_map_maximalIdeal B n hnpos hn A hindex E hE
    hbounds P hP hfinite Q hQ hclosed
  have hlocal : IsLocalHom (algebraMap A (Localization.AtPrime Q)) :=
    ((IsLocalRing.local_hom_TFAE _).out 3 1).mp (le_of_eq hmax)
  have hsep := dvr_tame_tensor_factor_residue_isSeparable B n hnpos hn A hindex E hE
    hbounds P hP hfinite Q hQ hclosed hlocal
  have : Module.Finite A (integralClosure A F) := hfinite
  have : Algebra.EssFiniteType A (Localization.AtPrime Q) :=
    Algebra.EssFiniteType.comp A (integralClosure A F) (Localization.AtPrime Q)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax

end RingTheory
