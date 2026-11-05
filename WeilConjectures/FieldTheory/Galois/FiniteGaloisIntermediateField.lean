/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Order.Interval.Finset.Defs

/-!
# The lattice of finite Galois subextensions of a Galois extension

Let `Ω/L` be a Galois extension (possibly infinite) and `J` the lattice of finite Galois
subextensions of `Ω/L` (`FiniteGaloisIntermediateField L Ω`).

* `J` is a locally finite order: a finite Galois extension has finitely many intermediate fields
  (`FiniteGaloisIntermediateField.instLocallyFiniteOrder`).
* For `k, j ∈ J`, the image `N j k` of `Gal(Ω/k)` in `Gal(j/L)`
  (`FiniteGaloisIntermediateField.restrictFixingSubgroup`) is a normal subgroup, with
  `N j k ⊔ N j m = N j (k ⊓ m)` (by the Galois correspondence of `Ω/L`), `N j j = ⊥` and
  `N j ⊥ = ⊤`.
* For `k ≤ j` and lifts `c a ∈ Gal(Ω/L)` of the elements `a ∈ Gal(k/L)`, the map
  `(a, n) ↦ (c a)|_j * n` is a bijection `Gal(k/L) × N j k ≃ Gal(j/L)`
  (`FiniteGaloisIntermediateField.bijective_restrictNormalHom_mul`).
-/

@[expose] public section

open IntermediateField

namespace FiniteGaloisIntermediateField

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

variable [IsGalois L Ω]

end FiniteGaloisIntermediateField
