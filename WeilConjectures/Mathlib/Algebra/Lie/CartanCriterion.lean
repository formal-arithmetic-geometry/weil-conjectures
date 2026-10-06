/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import WeilConjectures.Mathlib.Algebra.Lie.Engel
public import WeilConjectures.Mathlib.Algebra.Lie.Solvable

/-!
# Cartan's criteria for Lie algebras of endomorphisms

This file states Cartan's trace criterion for a Lie algebra of endomorphisms of a
finite-dimensional vector space, and the non-degeneracy of the Killing form of a Lie algebra with
trivial radical, in the forms used by the blueprint.

## Main declarations

* `LieSubalgebra.isSolvable_of_trace_mul_eq_zero`: **Cartan's trace criterion**: a Lie algebra
  `A` of endomorphisms with `tr (X Y) = 0` for all `X ∈ ⁅A, A⁆` and `Y ∈ A` is solvable.
* `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate`: the Killing form of a
  finite-dimensional characteristic-zero Lie algebra with trivial radical is non-degenerate.

## Blueprint

* `LieSubalgebra.isSolvable_of_trace_mul_eq_zero` implements `lem-wf-cartan-trace-criterion`.
* `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate` implements
  `lem-ag-killing-nondegenerate`.
-/

@[expose] public section

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {k M : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]
  [FiniteDimensional k M]

/-- **Cartan's trace criterion.** Let `A` be a Lie algebra of endomorphisms of a
finite-dimensional vector space `M` over a field of characteristic zero. If `tr (X Y) = 0` for all
`X ∈ ⁅A, A⁆` and `Y ∈ A`, then `A` is solvable.
(blueprint: `lem-wf-cartan-trace-criterion`) -/
theorem isSolvable_of_trace_mul_eq_zero (A : LieSubalgebra k (Module.End k M))
    (h : ∀ X ∈ derivedSeries k A 1, ∀ Y : A,
      LinearMap.trace k M ((X : Module.End k M) * Y) = 0) :
    IsSolvable A := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton A := inferInstance
    infer_instance
  set D := derivedSeries k A 1
  have hD : traceForm k D M = 0 := by
    ext X Y
    exact h X X.2 Y
  have hDD := isNilpotent_derivedSeries_of_traceForm_eq_zero hD
  set DD := derivedSeries k D 1
  have hS : LieRing.IsNilpotent (toEnd k DD M).range := by
    refine ((toEnd k DD M).range.exists_forall_apply_eq_zero_and_isNilpotent ?_).2
    rintro _ ⟨X, rfl⟩
    exact isNilpotent_toEnd_of_isNilpotent k DD M X
  have : IsSolvable DD := Function.Injective.lieAlgebra_isSolvable
    (f := (toEnd k DD M).rangeRestrict) fun X Y hXY ↦ by
      have hXY := Subtype.ext_iff.mp hXY
      exact Subtype.ext <| Subtype.ext <| Subtype.ext hXY
  have : IsSolvable D := isSolvable_of_isSolvable_derivedSeries_one (R := k)
  exact isSolvable_of_isSolvable_derivedSeries_one (R := k)

end LieSubalgebra

namespace LieAlgebra.HasTrivialRadical

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]

/-- The Killing form of a finite-dimensional Lie algebra with trivial radical over a field of
characteristic zero is non-degenerate. This is Cartan's criterion for semisimplicity,
`LieAlgebra.HasTrivialRadical.instIsKilling`.
(blueprint: `lem-ag-killing-nondegenerate`) -/
theorem killingForm_nondegenerate [HasTrivialRadical k L] : (killingForm k L).Nondegenerate :=
  IsKilling.killingForm_nondegenerate k L

end LieAlgebra.HasTrivialRadical
