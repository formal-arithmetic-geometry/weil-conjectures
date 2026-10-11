/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Proper zero-dimensional schemes over a field

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0)
(blueprint: lem-pc-dim-zero-finite-over-field)
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper zero-dimensional scheme over a field is finite and affine, and has
finite-dimensional global sections.

Source: Stacks Project, Varieties, Tag 06LH (Lemma algebraic-scheme-dim-0),
algebraic case (blueprint: lem-pc-dim-zero-finite-over-field).

The proof first uses [pqf-lem-proper-basic] to obtain finite type from properness.
Then [lem-pc-algebraic-dim-zero-affine-finite] gives affineness and finiteness
from finite type and dimension at most zero. Finally,
[lem-weil-pbc-finite-over-field-affine-finite-dim] gives the finite-dimensional
global sections of a scheme finite over `Spec k`.
-/
theorem proper_dim_zero_finite_over_field {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [IsProper f] (hY : Y.dim ≤ 0) :
    IsFinite f ∧ IsAffine Y ∧
      (letI := f.ΓAlgebra; Module.Finite k Γ(Y, ⊤)) := by
  sorry

end AlgebraicGeometry
