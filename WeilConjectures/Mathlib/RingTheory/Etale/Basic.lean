/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Basic

/-!
# Tensor products of étale algebras

The tensor product of two étale `R`-algebras is étale over `R`.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.Etale

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The tensor product of two étale `R`-algebras is étale over `R`: it is a base change of
`B` to `A`, followed by `R → A`. -/
instance tensorProduct [Etale R A] [Etale R B] : Etale R (A ⊗[R] B) :=
  comp R A (A ⊗[R] B)

end Algebra.Etale
