/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials in the restriction of an endomorphism to an invariant submodule

## Main results

- `Module.End.aeval_restrict` — evaluating a polynomial at the restriction of an endomorphism to
  an invariant submodule is the restriction of its evaluation at the endomorphism.
-/

@[expose] public section

open Polynomial

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Evaluating a polynomial `q` at the restriction of `f` to an `f`-invariant submodule `p` is the
restriction of `q` evaluated at `f`. This is the `Polynomial.aeval` version of
`Module.End.pow_restrict`. -/
theorem aeval_restrict {p : Submodule R M} {f : Module.End R M} (h : ∀ x ∈ p, f x ∈ p) (q : R[X])
    (h' : ∀ x ∈ p, (aeval f q) x ∈ p) :
    aeval (f.restrict h) q = (aeval f q).restrict h' := by
  have key (q : R[X]) (x : p) : ((aeval (f.restrict h) q) x : M) = aeval f q x := by
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb]
    | monomial n c => simp [aeval_monomial, Module.End.pow_restrict n h]
  ext x
  exact key q x

end Module.End
