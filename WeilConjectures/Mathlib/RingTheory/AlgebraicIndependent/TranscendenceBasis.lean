/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The transcendence degree of a field of fractions

## Main results

* `IsFractionRing.trdeg_eq`: for a domain `A` with field of fractions `K`, both seen as algebras
  over a base ring `R`, the transcendence degrees `Algebra.trdeg R K` and `Algebra.trdeg R A`
  agree. Indeed `K` is algebraic over `A`, so it contributes nothing to the transcendence degree.
* `IsFractionRing.lift_trdeg_eq`: the same statement for `A` and `K` in different universes.
-/

@[expose] public section

universe v w

/-- The transcendence degree of a domain over a base ring agrees with the transcendence degree
of its field of fractions. This is the version for `A` and `K` in different universes; see
`IsFractionRing.trdeg_eq` for the version without universe lifts. -/
theorem IsFractionRing.lift_trdeg_eq (R : Type*) (A : Type v) (K : Type w) [CommRing R]
    [CommRing A] [IsDomain A] [Field K] [Algebra R A] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] [IsFractionRing A K] [Nontrivial R] [FaithfulSMul R A] :
    Cardinal.lift.{v} (Algebra.trdeg R K) = Cardinal.lift.{w} (Algebra.trdeg R A) := by
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have hz : Algebra.trdeg A K = 0 := trdeg_eq_zero
  have h := lift_trdeg_add_eq R A K
  rw [hz, Cardinal.lift_zero, add_zero] at h
  exact h.symm

/-- The transcendence degree of a domain over a base ring agrees with the transcendence degree
of its field of fractions. -/
theorem IsFractionRing.trdeg_eq (R : Type*) (A K : Type v) [CommRing R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [IsFractionRing A K]
    [Nontrivial R] [FaithfulSMul R A] :
    Algebra.trdeg R K = Algebra.trdeg R A := by
  simpa using IsFractionRing.lift_trdeg_eq R A K
