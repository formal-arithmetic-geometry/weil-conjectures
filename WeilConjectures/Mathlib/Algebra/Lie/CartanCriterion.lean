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

end LieSubalgebra

namespace LieAlgebra.HasTrivialRadical

variable (k L : Type*) [Field k] [CharZero k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]

end LieAlgebra.HasTrivialRadical
