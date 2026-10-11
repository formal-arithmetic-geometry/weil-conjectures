/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.ReesAlgebra

/-!
# The Rees algebra of a finitely generated ideal is of finite type

Mathlib records `Algebra.FiniteType R (reesAlgebra I)` only as an instance under
`[IsNoetherianRing R]`. The underlying argument only uses that `I` is finitely generated,
which is what `reesAlgebra.finiteType` below states.
-/

@[expose] public section

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- The Rees algebra of a finitely generated ideal is of finite type over the base ring.
This generalizes the `IsNoetherianRing` instance in Mathlib. -/
theorem reesAlgebra.finiteType (hI : I.FG) : Algebra.FiniteType R (reesAlgebra I) :=
  ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
