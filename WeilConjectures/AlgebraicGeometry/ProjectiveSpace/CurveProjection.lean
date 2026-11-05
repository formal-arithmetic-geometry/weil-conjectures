/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
public import WeilConjectures.RingTheory.GradedAlgebra.LinearPair

/-!
# Finite projections of projective curves to the projective line

Let `k` be an infinite field and `X` an integral closed subscheme of a projective space over
`k` of dimension one. Then there is a finite morphism `X ⟶ ℙ¹_k` over `k`.

The proof goes through the homogeneous coordinate ring: `X ≅ Proj S` for a standard graded
`k`-algebra `S` which is a domain; since `Proj S` has dimension one, there are linear forms
`l₀, l₁ ∈ S₁` without common zero on `Proj S`, and the linear projection
`π_{l₀,l₁} : Proj S ⟶ ℙ¹_k` is finite.

## Main statements

- `AlgebraicGeometry.exists_isStandard_iso_proj` — the homogeneous coordinate ring of an
  integral closed subscheme of projective space.
- `AlgebraicGeometry.exists_isFinite_toProjectiveLine` — a projective curve over an infinite
  field admits a finite morphism to `ℙ¹_k`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
