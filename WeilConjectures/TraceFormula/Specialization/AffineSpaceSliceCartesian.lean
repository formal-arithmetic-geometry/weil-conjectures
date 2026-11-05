/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice

/-!

# The coordinate generic slice is cartesian

For a coordinate `i : Fin (n + 1)`, let `πᵢ : 𝔸ⁿ⁺¹_S ⟶ 𝔸¹_S` be the `i`-th coordinate projection
over `S = Spec k'⟦t⟧` (`AlgebraicGeometry.affineSpaceCoordinate`). The coordinate generic slice
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`AlgebraicGeometry.affineSpaceSlice`) identifies `𝔸ⁿ_{K⟦t⟧}` with the
base change of `πᵢ` along the generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`
(`AlgebraicGeometry.traitSlice`): the square
```
𝔸ⁿ_{K⟦t⟧} ──hᵢ──→ 𝔸ⁿ⁺¹_S
    │                │ πᵢ
Spec K⟦t⟧ ───σ───→ 𝔸¹_S
```
is cartesian (`AlgebraicGeometry.isPullback_affineSpaceSlice`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

end AlgebraicGeometry
