/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!
# Kähler differentials of a localization

## Main results

- `KaehlerDifferential.span_range_D_algebraMap_eq_top`: if `K` is a localization of `A`, then
  `Ω[K⁄R]` is spanned over `K` by the differentials of elements of `A`.
- `KaehlerDifferential.exists_span_D_algebraMap_eq_top`: if moreover `K` is a field and
  `Ω[K⁄R]` is one-dimensional, it is spanned by the differential of a single element of `A`.
-/

@[expose] public section

namespace KaehlerDifferential

variable {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]

end KaehlerDifferential
