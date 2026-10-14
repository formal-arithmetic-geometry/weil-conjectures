/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # The local maximal-ideal conclusion of Abhyankar's lemma

Source: Stacks Project, Tags 0BRM, 09EM and 09E7.
(blueprint: lem-sbc-dvr-abhyankar-local-maximal-ideal) -/

@[expose] public section

universe u
namespace RingTheory

/-- A tame local DVR extension becomes weakly unramified after divisible base change.

Source: Stacks Project, Tag 0BRM, with the normalization diagram of 09EM and
its weak-unramifiedness consequence in 09E7.
(blueprint: lem-sbc-dvr-abhyankar-local-maximal-ideal)

Proof: Faithfulness, finiteness and normality identify A with the integral
closure of B in Frac(A). The maximal-ideal identities give base index n and
tame index e. The unit condition on e and residue separability are exactly
tameness. The maps from E and A into F extend to the two fraction fields;
the generation hypothesis makes F a field factor of E tensor Frac(A) over
Frac(B). The local map j selects a center of this factor over U. A DVR T
with fraction field F dominating U and A is the corresponding localization
of the normalization: the normalization is contained in the integrally
closed T, and localization at its center is a DVR contained in T with the
same fraction field. Such an inclusion of valuation rings is an equality,
since T is not a field and the only proper coarsening of a discrete rank-one
valuation is the trivial valuation. Apply 0BRM with e dividing n. Explicitly,
write a B-uniformizer as v times the n-th power of an A-uniformizer and
adjoin an e-th root of the unit v by a finite etale extension of A. This
reduces to a base field containing an e-th root of the B-uniformizer. In
that root extension, its quotient by a U-uniformizer is an e-th root of a
unit, so the normalized extension of U is etale. Multiplicativity of
indices gives index one over the root base. Tag 09EQ preserves adic formal
smoothness under the remaining normalized base change, and the finite etale
unit-root extension permits descent as in 0BRM. Thus A -> T is adically
formally smooth. Tag 09E7 gives weak unramifiedness: the image of an
A-uniformizer generates the maximal ideal of T. This is the displayed
maximal-ideal equality. -/
theorem dvr_abhyankar_local_map_maximalIdeal
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra B U] [IsLocalHom (algebraMap B U)]
    (e : ℕ) (he : IsUnit (e : B)) (hedvd : e ∣ n)
    (hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ e)
    (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U))
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Algebra U E] [IsFractionRing U E] [IsScalarTower B U E]
    (F : Type u) [Field F] [Algebra A F] (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    (T : Type u) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsLocalHom (algebraMap A T)]
    [Algebra T F] [IsFractionRing T F] [IsScalarTower A T F]
    (j : U →+* T) (hj : IsLocalHom j)
    (hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b))
    (hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A T) = IsLocalRing.maximalIdeal T := by sorry

end RingTheory
