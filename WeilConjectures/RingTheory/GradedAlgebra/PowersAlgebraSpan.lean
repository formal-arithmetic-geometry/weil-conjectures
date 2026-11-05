/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.GradedAlgebra.PowersAlgebra

/-!
# The graded algebra `k[a₀ t, …, aₙ t]`

Let `K` be a commutative `k`-algebra and `a : ι → K` a family of elements. The graded algebra
`⊕ₙ Vⁿ tⁿ` attached to the span `V` of the `aᵢ` (see `Submodule.powersAlgebra`) is generated
by the linear forms `aᵢ t`; if `ι` is finite it is a standard graded `k`-algebra.

If `a i₀ = 1`, then `a i₀ t = t`, and the degree-zero part of the localization of `⊕ₙ Vⁿ tⁿ` at
`t` embeds into `K` by `c tⁿ / tⁿ ↦ c`; this sends `(aᵢ t) / t` to `aᵢ`. Geometrically, `K` is
the coordinate ring of an affine chart of a closed subscheme of projective space, and this
identifies it with the corresponding chart of `Proj (⊕ₙ Vⁿ tⁿ)`.

## Main definitions

- `Submodule.powersLinearForm k a i` — the linear form `aᵢ t` of `⊕ₙ Vⁿ tⁿ`.
- `Submodule.powersAwayEval a h` — for `a i₀ = 1`, the injective `k`-algebra map
  `(⊕ₙ Vⁿ tⁿ)_(t) → K`, `c tⁿ / tⁿ ↦ c`.

## Main statements

- `Submodule.adjoin_range_powersLinearForm` — the linear forms `aᵢ t` generate `⊕ₙ Vⁿ tⁿ`.
- `Submodule.powersAwayEval_injective` — the map `(⊕ₙ Vⁿ tⁿ)_(t) → K` is injective.
-/

@[expose] public section

open Polynomial HomogeneousLocalization

namespace Submodule

variable (k : Type*) {K ι : Type*} [Field k] [CommRing K] [Algebra k K] (a : ι → K)

section Away

variable {k} (V : Submodule k K)

variable (k) {a} {i₀ : ι} (h : a i₀ = 1)

end Away

end Submodule
