/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
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

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # A local consequence of tame DVR base change

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-residue-separable) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Residue separability after tame DVR base change.

Source: Stacks Project, Tags 032L, 0BRM and 09E7.
(blueprint: lem-sbc-dvr-tame-tensor-factor-residue-separable)

Proof: Finite faithfulness gives an injection B -> A and a finite extension
Frac(A)/Frac(B); normality of A identifies A with the normalization of B in
Frac(A). The maximal-ideal identity gives ramification index n. The kernel of
A -> F is prime and contracts to zero in B, since B embeds in E and the map
from the field E to the nonzero tensor quotient F is injective. Incomparability
for the integral extension B -> A then makes that kernel zero. Inverting the
nonzero elements identifies F with a field factor of E tensor_Frac(B) Frac(A).
The normalization C of B in E is finite by Stacks 032L (the separable trace
argument); it is a Dedekind domain, so C localized at a prime over m_B is a DVR.
At each such prime, the two divisibility bounds and the unit n imply that the
ramification index and the residue degree are prime to the residue characteristic.
The inseparable residue degree is a power of that characteristic and divides
the residue degree, hence is one; in characteristic zero separability is automatic.
Apply Abhyankar's lemma 0BRM to these tame DVRs and Frac(A)/Frac(B): their
ramification indices divide n, the base-change index. Integrality over A and B
in F agrees by transitivity and the integral extension A/B. Localization of
normalization therefore identifies S_Q with the normalized field factor of
0BRM. Finiteness of S over A, its normality, and the fact that Q lies over m_A
ensure that S_Q is a DVR. Abhyankar gives adic formal smoothness of A -> S_Q;
Stacks 09E7 identifies its two consequences as index one and residue separability.
The residue-separability consequence of 09E7 is separability for the residue
map induced by A -> S_Q. The explicit local-hom proof only supplies that map's
Lean algebra structure; it adds no ramification hypothesis. This is only the
residue-field conclusion and makes no assertion about the maximal ideal. -/
theorem dvr_tame_tensor_factor_residue_isSeparable
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
      ∀ (hloc : IsLocalHom (algebraMap A (Localization.AtPrime Q))),
      letI := hloc
      Algebra.IsSeparable (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by sorry

end RingTheory
