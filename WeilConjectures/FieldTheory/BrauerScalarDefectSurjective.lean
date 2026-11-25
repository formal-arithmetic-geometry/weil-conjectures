/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CrossedProductRealization

/-!
# Crossed-product realization of continuous degree-two classes

Every continuous degree-two Galois cohomology class with values in the units of the separable
closure is realized by the matrix scalar defects of a central simple algebra.

## Main results

- `Field.exists_csa_brauerScalarDefect`: every class in `GaloisUnitsH2 K` is realized by some
  central simple algebra.

## Implementation details

A homogeneous cycle representing the class is turned into a continuous two-cocycle, which is
inflated from a normalized cocycle on `Gal(L/K)` for a finite Galois extension `L`. The crossed
product of `L` by that cocycle is the required central simple algebra, split over `L`; the
construction itself is `Field.exists_crossedProduct_realization_data`.

## References

* Stacks Project, Theorem 03R7 (surjectivity) and Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

/-- Every continuous degree-two Galois class is realized by matrix scalar defects
of a central simple algebra. -/
theorem exists_csa_brauerScalarDefect (K : Type u) [Field K] (x : GaloisUnitsH2 K) :
    ∃ A : CSA.{u, u} K, HasBrauerScalarDefect K A x := by
  obtain ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩ :=
    exists_crossedProduct_realization_data K x
  exact ⟨A, n, hn, e, b, hb, z, hz, hdesc, hdefect⟩

end Field
