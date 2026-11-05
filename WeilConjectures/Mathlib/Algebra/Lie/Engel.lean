/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Engel

/-!
# Engel's theorem for Lie algebras of nilpotent endomorphisms

This file records the classical matrix form of Engel's theorem: a Lie algebra of nilpotent
endomorphisms of a nonzero finite-dimensional vector space has a common null vector and is
nilpotent. It is a direct consequence of Mathlib's `LieModule.isNilpotent_iff_forall'`.

## Main declarations

* `LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent`: Engel's matrix lemma.

## Blueprint

`LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent` implements `lem-wf-engel-matrix`.
-/

@[expose] public section

open LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

end LieSubalgebra
