/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.RingTheory.Trace.Basic

/-!
# Generators of Galois extensions of prime degree

Let `M/L` be a Galois extension of prime degree `p`.

* `IsGalois.exists_not_mem_range_pow_sub_self_mem_range`: if `L` has characteristic `p`, then
  `M` contains an element `θ ∉ L` with `θ ^ p - θ ∈ L` (Artin–Schreier generator). The proof is
  additive Hilbert 90: for a generator `σ` of `Gal(M/L)`, the image of `σ - 1` is the kernel of
  the trace, which contains `1`.
* `IsGalois.exists_not_mem_range_pow_mem_range`: if `L` contains a primitive `p`-th root of
  unity, then `M` contains an element `θ ∉ L` with `θ ^ p ∈ L` (Kummer generator).
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace IsGalois

variable {L M : Type*} [Field L] [Field M] [Algebra L M]

end IsGalois
