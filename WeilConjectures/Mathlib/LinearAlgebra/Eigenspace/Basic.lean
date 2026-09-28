/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues on a subquotient

The eigenvalues of an endomorphism on any of its invariant subquotients occur among its
eigenvalues on the ambient space.

## Main declarations

* `Module.End.hasEigenvalue_of_subquotient`: a scalar acting on a nonzero invariant subquotient is
  an eigenvalue of the ambient endomorphism.

## Blueprint

`Module.End.hasEigenvalue_of_subquotient` implements part of `sk-p-linear-filtration`.
-/

@[expose] public section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If a scalar `c` acts on a nonzero invariant subquotient `S ⧸ U` of `V`, then `c` is an
eigenvalue of the endomorphism on all of `V`.
(blueprint: `sk-p-linear-filtration`) -/
theorem hasEigenvalue_of_subquotient (f : Module.End K V) {U S : Submodule K V} (hUS : U < S)
    (hU : U ≤ U.comap f) (hS : S ≤ S.comap f) (c : K) (hc : ∀ x ∈ S, f x - c • x ∈ U) :
    f.HasEigenvalue c := by
  sorry

end Module.End
