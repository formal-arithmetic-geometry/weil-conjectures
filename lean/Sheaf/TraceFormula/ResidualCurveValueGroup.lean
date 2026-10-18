/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Sheaf.RingTheory.ValuationComapResidue
import Sheaf.GroupTheory.RationalRankZeroTorsion

/-!
# Values in a residually transcendental curve extension

Source: Temkin, *Stable modification of relative curves*, Proposition 4.3.1,
proof, first stage, p. 28 (blueprint: lem-trf-residual-curve-value-group).
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- Every value in a residually transcendental curve extension over a separably
closed field is represented by a ground-field element. Integral and maximal-ideal
values have representatives in the corresponding restricted valuation ring ideals.

Source: Temkin, Proposition 4.3.1, proof, first stage, p. 28.
(blueprint: lem-trf-residual-curve-value-group)

Proof:
1. Put `R = O.comap (algebraMap K L)`. The relative Abhyankar inequality
   (lem-trf-abhyankar-inequality) and both transcendence-degree-one hypotheses
   give rational rank zero for the quotient of the two value groups.
2. By lem-trf-rational-rank-zero-torsion, this quotient is torsion.
3. By lem-trf-separably-closed-value-group-divisible, the ground-field value group
   is divisible. For a value alpha of `L`, choose a positive integer n with n alpha
   in the ground value group, and divide n alpha there by n. The ambient ordered
   group is torsion-free, so the result equals alpha. A ground-field representative
   c therefore has z/c a unit of O.
4. If z belongs to O, the equality c = z (z/c)⁻¹ places c in R. If z is in the
   maximal ideal of O and c were a unit of R, its image and z/c would both be
   units of O, contradicting that z is a nonunit. This proves both refinements.
-/
theorem residual_curve_value_group
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [IsSepClosed K]
    (hfg : (⊤ : IntermediateField K L).FG)
    (htrdeg : Algebra.trdeg K L = 1) (O : ValuationSubring L)
    (hres : @Algebra.trdeg
      (IsLocalRing.ResidueField (O.comap (algebraMap K L)))
      (IsLocalRing.ResidueField O) _ _ (O.comapResidueAlgebra (algebraMap K L)) = 1) :
    (∀ z : Lˣ, ∃ c : Kˣ, ∃ a : Oˣ,
      ((a : O) : L) = (z : L) / algebraMap K L (c : K)) ∧
    (∀ z : O, z ≠ 0 → ∃ c : O.comap (algebraMap K L), c ≠ 0 ∧ ∃ a : Oˣ,
      ((a : O) : L) = (z : L) / algebraMap K L (c : K)) ∧
    (∀ z : O, z ∈ IsLocalRing.maximalIdeal O → z ≠ 0 →
      ∃ c : O.comap (algebraMap K L),
        c ∈ IsLocalRing.maximalIdeal (O.comap (algebraMap K L)) ∧ c ≠ 0 ∧ ∃ a : Oˣ,
          ((a : O) : L) = (z : L) / algebraMap K L (c : K)) := by
  sorry
