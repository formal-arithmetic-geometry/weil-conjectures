/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Substituting a polynomial into a characteristic polynomial

`Matrix.charpoly_comp` computes `M.charpoly.comp q` as the determinant of `q - M`, generalizing
`Matrix.eval_charpoly` from scalars to polynomials.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- Substituting a polynomial `q` into the characteristic polynomial of `M` gives the
determinant of `q - M`. -/
theorem charpoly_comp (M : Matrix n n R) (q : R[X]) :
    M.charpoly.comp q = (Matrix.scalar n q - M.map C).det := by
  rw [show M.charpoly.comp q = eval₂RingHom C q M.charpoly from rfl, Matrix.charpoly,
    RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

end Matrix
