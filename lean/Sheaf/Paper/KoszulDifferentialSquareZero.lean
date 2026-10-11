/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.KoszulDifferential
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The Koszul differential squares to zero

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Definition
Tag 0622 (blueprint: lem-weil-pbc-koszul-differential-square-zero).

The Koszul differential `D_φ` is the one named map
`CliffordAlgebra.contractLeft φ` at the zero quadratic form on `ExteriorAlgebra R E`
(STATE line KOSZUL); by the proof of `ExteriorAlgebra.koszul_differential`
(lem-weil-pbc-koszul-differential, step 1) it is the unique map of that node.
-/

@[expose] public section

universe u v

namespace ExteriorAlgebra

/--
The Koszul differential has square zero, and hence so do its restrictions to
the homogeneous exterior powers. Source: Stacks Project, More on Algebra,
Definition Tag 0622 and the paragraph following it (blueprint:
lem-weil-pbc-koszul-differential-square-zero).
(blueprint: lem-weil-pbc-koszul-differential-square-zero)

Proof: on a wedge monomial, apply the recursive formula twice; the two scalar
terms cancel and the remaining term is the wedge of the first vector with the
square on the shorter monomial. Induction starts at `1`. Wedge monomials span
the exterior algebra, so linearity gives `D.comp D = 0`; restricting this
identity to each homogeneous exterior power gives the final clause.
-/
theorem koszul_differential_square_zero
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) :
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ).comp
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ) = 0 ∧
      ∀ (n : ℕ) (x : ⋀[R]^(n + 1) E),
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ
            (x : ExteriorAlgebra R E)) = 0 := by
  sorry

end ExteriorAlgebra
