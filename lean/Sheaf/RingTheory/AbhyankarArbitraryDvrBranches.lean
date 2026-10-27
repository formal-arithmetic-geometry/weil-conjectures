/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.FieldTheory.SeparableExtension

import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Localization.Integral

/-! # Abhyankar cancellation for arbitrary local DVR extensions

Source: Stacks Project, Tags 0BRM (lemma-abhyankar), 09E7 and 09EM.
(blueprint: lem-sfb-abhyankar-arbitrary-dvr-branches).

The normalization map below is the restriction of the right tensor inclusion followed
by reduction. No module finiteness is imposed on either normalization.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uK uL uN

open scoped TensorProduct

namespace RingTheory

/-- The reduced generic tensor algebra in the normalization diagram of Stacks Tag 09EM.
Source: Stacks Project, Tags 09EM and 0BRM.
(blueprint: lem-sfb-abhyankar-arbitrary-dvr-branches). -/
abbrev AbhyankarReducedTensor (K : Type uK) (L : Type uL) (N : Type uN)
    [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N] :=
  (L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)

/-- The canonical map between the normalizations, sending `x` to the reduction of `1 ⊗ x`.
Integrality is preserved by the tensor inclusion and by extension of the base from A to B.
Source: Stacks Project, Tag 09EM, normalization diagram used in Tag 0BRM.
(blueprint: lem-sfb-abhyankar-arbitrary-dvr-branches). -/
noncomputable def abhyankarNormalizationMap
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (N : Type uN)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field N]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K N] [Algebra A N] [IsScalarTower A K N] :
    integralClosure A N →+* integralClosure B (AbhyankarReducedTensor K L N) where
  toFun x := ⟨Ideal.Quotient.mk (nilradical (L ⊗[K] N))
      (Algebra.TensorProduct.includeRight (x : N)),
    (x.property.map ((Ideal.Quotient.mkₐ A (nilradical (L ⊗[K] N))).comp
      (Algebra.TensorProduct.includeRight.restrictScalars A))).tower_top⟩
  map_zero' := Subtype.ext (map_zero
    ((Ideal.Quotient.mk (nilradical (L ⊗[K] N))).comp
      (Algebra.TensorProduct.includeRight : N →ₐ[K] L ⊗[K] N).toRingHom))
  map_one' := Subtype.ext (map_one
    ((Ideal.Quotient.mk (nilradical (L ⊗[K] N))).comp
      (Algebra.TensorProduct.includeRight : N →ₐ[K] L ⊗[K] N).toRingHom))
  map_add' x y := Subtype.ext (map_add
    ((Ideal.Quotient.mk (nilradical (L ⊗[K] N))).comp
      (Algebra.TensorProduct.includeRight : N →ₐ[K] L ⊗[K] N).toRingHom) (x : N) (y : N))
  map_mul' x y := Subtype.ext (map_mul
    ((Ideal.Quotient.mk (nilradical (L ⊗[K] N))).comp
      (Algebra.TensorProduct.includeRight : N →ₐ[K] L ⊗[K] N).toRingHom) (x : N) (y : N))

/-- Tame ramification cancels on every local normalized branch after a finite extension
whose local ramification index is divisible by the original index.
Source: Stacks Project, Tag 0BRM; maximal-ideal consequence via Tag 09E7;
normalizations and branches as in Tag 09EM.
(blueprint: lem-sfb-abhyankar-arbitrary-dvr-branches).

Proof:
1. Apply lem-sfb-dvr-algebraic-normalization-structure, case (a), to N/K.
   The contracted ideal n is maximal and R_n and C_q are DVRs. Their fraction fields
   are N and the selected field factor F of the reduced generic tensor algebra:
   scaling a monic equation by a power of a uniformizer makes any algebraic element
   integral. The induced local map R_n -> C_q is injective since N -> F is a field map.
2. Suppose e divides d. Write an A-uniformizer pi as u*tau^d in R_n. The residue
   characteristic hypothesis makes e invertible. Apply lem-sfb-dvr-unit-root-normalized-lift
   to adjoin r with r^e=u, obtaining compatible finite separable extensions N_2 and F_2
   and local DVRs S_2 and T_2 with unchanged maximal ideals. Then theta=r*tau^(d/e)
   satisfies theta^e=pi.
3. By lem-sbc-dvr-uniformizer-root-algebra, D=A[theta] is a DVR with uniformizer theta,
   fraction field K_0=K(theta), and residue field kappa(A). It is the integral closure
   of A in K_0: a DVR is integrally closed, and integrality over A implies integrality
   over D.
4. Write pi=w*varpi^e in B. Substituting X=varpi*Y identifies L tensor_K K_0 with
   L[Y]/(Y^e-w). By lem-sfb-unit-binomial-finite-etale, H=B[Y]/(Y^e-w) is finite etale.
   By lem-sfb-finite-etale-normal-generic-components it is the integral closure of B
   in that generic algebra. The embedding into F_2 selects a generic field F_0 and
   a local branch V. The contracted prime contains varpi, so is nonzero and maximal;
   lem-sfb-dvr-algebraic-normalization-structure makes V a DVR.
5. By lem-weil-pbc-etale-fibre-discrete-separable-points, m_B V=m_V and kappa(V)/kappa(B)
   is finite separable. Computing the valuation of pi along A -> B -> V and A -> D -> V
   gives e=e*a, so a=1. The residue extension kappa(V)/kappa(D) is separable by
   lem-sfb-separable-finite-top-extension in positive characteristic and by
   lem-weil-pbc-char-zero-field-extension-separable in characteristic zero.
6. Apply the unconditional local clause of lem-sfb-dvr-index-one-separable-base-change
   to D -> V and N_2/K_0. Tensor associativity and the field image generated by L,N,r
   identify its selected generic field with F_2. By lem-weil-pbc-integral-transitive,
   normalizing first over D or over A agrees, as does normalizing B in stages through
   F_0. By lem-weil-pbc-integral-closure-commutes-localization the local branches are
   S_2 and T_2. Thus m_{S_2} T_2=m_{T_2}. No Noetherian tensor hypothesis is used.
7. The element tau remains a uniformizer in S_2, hence in T_2. Write tau=v*rho^b
   in T=C_q. Its valuation in T_2 gives 1=b*v_{T_2}(rho); both factors are positive
   integers, so b=1. Thus tau generates m_T. Since m_{R_n}=nR_n and all denominators
   outside n become units in C_q, this is exactly nC_q=qC_q.
-/
theorem abhyankar_arbitrary_dvr_branches
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    [IsLocalHom (algebraMap A B)]
    (K : Type uK) (L : Type uL) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (e : ℕ) (he : 1 ≤ e)
    (hindex : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B ^ e)
    (htame : CharZero (IsLocalRing.ResidueField A) ∨
      ∃ p : ℕ, Nat.Prime p ∧ CharP (IsLocalRing.ResidueField A) p ∧ ¬ p ∣ e ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B))
    (N : Type uN) [Field N] [Algebra K N] [FiniteDimensional K N]
    [Algebra A N] [IsScalarTower A K N]
    (q : Ideal (integralClosure B (AbhyankarReducedTensor K L N))) [q.IsMaximal] :
    (q.comap (abhyankarNormalizationMap A B K L N)).IsMaximal ∧
    ∃ (_hR : IsDomain (Localization.AtPrime
        (q.comap (abhyankarNormalizationMap A B K L N))))
      (_hC : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime
        (q.comap (abhyankarNormalizationMap A B K L N))) ∧
      IsDiscreteValuationRing (Localization.AtPrime q) ∧
      ∀ (d : ℕ), 1 ≤ d → e ∣ d →
        (IsLocalRing.maximalIdeal A).map
            ((algebraMap (integralClosure A N) (Localization.AtPrime
              (q.comap (abhyankarNormalizationMap A B K L N)))).comp
                (algebraMap A (integralClosure A N))) =
          ((q.comap (abhyankarNormalizationMap A B K L N)).map
            (algebraMap (integralClosure A N) (Localization.AtPrime
              (q.comap (abhyankarNormalizationMap A B K L N))))) ^ d →
        (q.comap (abhyankarNormalizationMap A B K L N)).map
            ((algebraMap (integralClosure B (AbhyankarReducedTensor K L N))
              (Localization.AtPrime q)).comp (abhyankarNormalizationMap A B K L N)) =
          q.map (algebraMap (integralClosure B (AbhyankarReducedTensor K L N))
            (Localization.AtPrime q)) := by
  sorry

end RingTheory
