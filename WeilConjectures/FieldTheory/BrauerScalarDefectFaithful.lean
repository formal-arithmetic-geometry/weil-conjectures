/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulForward
import WeilConjectures.FieldTheory.BrauerScalarDefectFaithfulBackward

/-!
# Faithfulness and independence of scalar-defect classes

Two scalar-defect classes of central simple algebras agree exactly when the algebras are Brauer
equivalent.

## Main results

- `Field.brauerScalarDefect_eq_iff`

## Implementation details

Changing a splitting conjugates the projective descent datum, and changing the matrix lifts
multiplies the scalar defect by a continuous coboundary, so the class is well defined; matrix
amplifications preserve the scalar defect, which gives the reverse implication. For the forward
implication, tensor the descent datum of `A` with that of `Bᵒᵖ`, adjust its lifts by the scalar
coboundary to obtain a genuine cocycle, descend to a finite Galois extension and apply matrix
Hilbert 90 to split `A ⊗ Bᵒᵖ`.

## References

* [Stacks Project, Theorem 03R7](https://stacks.math.columbia.edu/tag/03R7), homomorphism and
  injectivity arguments
* [Stacks Project, Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG) for the cochain
  convention
-/

@[expose] public section

universe u

namespace Field

/-- Two scalar-defect realizations give the same cohomology class exactly when their
algebras are Brauer equivalent. In particular the class of each algebra is unique. -/
theorem brauerScalarDefect_eq_iff (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (x y : GaloisUnitsH2 K)
    (hx : HasBrauerScalarDefect K A x) (hy : HasBrauerScalarDefect K B y) :
    x = y ↔ IsBrauerEquivalent A B := by
  constructor
  · intro hxy
    exact brauerEquivalent_of_brauerScalarDefect_eq K A B x y hx hy hxy
  · intro hAB
    exact brauerScalarDefect_eq_of_brauerEquivalent K A B x y hx hy hAB

end Field
