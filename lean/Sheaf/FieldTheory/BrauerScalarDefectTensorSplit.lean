/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker B2
-/
module

public import Sheaf.FieldTheory.BrauerScalarDefect

/-!
# Splitting the tensor product of scalar-defect realizations

Source: Stacks Project, Tag 03R7, injectivity argument, and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-tensor-split).
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

/-- Equal scalar-defect classes split the tensor product with the opposite algebra.

Proof: choose the matrix splittings and locally constant lifts supplied by the two
scalar-defect realizations. Transpose the second splitting to identify its opposite
with a matrix algebra, and use the inverse transpose of its lifts. The Kronecker
product with the first lifts realizes the tensor descent datum, with scalar defect
`c_z / c_w`. Equality of the two homogeneous cohomology classes says that `z - w`
is a continuous coboundary. Evaluate a homogeneous one-cochain witnessing this
boundary at `(1,g)` to obtain a locally constant scalar cochain `a(g)` with
`c_z(g,h) / c_w(g,h) = a(g) * g(a(h)) / a(g*h)`.
Rescale the tensor lifts by `a(g)⁻¹`; the new lifts are a genuine general-linear
one-cocycle. Compactness of the absolute Galois group and local constancy allow
all lifts, the scalar cochain, and the finitely many splitting coefficients to be
handled over a common finite Galois extension. Matrix Hilbert 90, equivalently
finite Galois descent of vector spaces, trivializes this cocycle. Conjugating the
tensor splitting by the trivializing matrix makes its descent datum coefficientwise
Galois action. Taking fixed points gives a K-algebra isomorphism from `A ⊗ Bᵐᵒᵖ`
to a matrix algebra over K. Its size is the product of the two positive splitting
sizes, hence is nonzero. No Brauer equivalence criterion is used in this step.
Source: Stacks Project, Tag 03R7, injectivity argument; Section 0DVG for the
homogeneous-to-inhomogeneous coboundary convention.
(blueprint: lem-sc-brauer-scalar-defect-tensor-split). -/
theorem tensor_opposite_split_of_brauerScalarDefect_eq (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y)
    (h : x = y) :
    ∃ n : ℕ, n ≠ 0 ∧ Nonempty ((A ⊗[K] Bᵐᵒᵖ) ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by sorry

end Field
