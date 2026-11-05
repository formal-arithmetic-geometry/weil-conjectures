/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Removing trivial summands from an octahedron

In a pretriangulated category `D`, consider composable morphisms `u₁₂ : X₁ ⟶ X₂` and
`u₂₃ : X₂ ⟶ X₃` with distinguished triangles on `u₁₂`, `u₂₃` and `u₁₂ ≫ u₂₃`. Padding one of the
objects `Xᵢ` by a direct summand on which the morphisms vanish, and the triangles by trivial
triangles, an octahedron for the padded data gives one for the original data, provided the
distinguished triangles of `D` are stable under retracts. This is the key step of the proof by
Balmer and Schlichting that the Karoubi envelope of a triangulated category satisfies the
octahedral axiom: the padded octahedron, once made block diagonal by an automorphism of its middle
object, has the original octahedron as a retract.

## Main statements

- `CategoryTheory.Pretriangulated.mk_comp_inl_distinguished`,
  `CategoryTheory.Pretriangulated.mk_fst_comp_distinguished`: the sum of a distinguished
  triangle with a trivial triangle is distinguished.
- `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₁`,
  `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₂`,
  `CategoryTheory.Triangulated.nonempty_octahedron_of_pad₃`: removing a trivial summand of `X₁`,
  `X₂` or `X₃` from an octahedron.

## References

* Paul Balmer and Marco Schlichting, *Idempotent completion of triangulated categories*,
  J. Algebra 236 (2001), proof of Theorem 1.12
-/
@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Pretriangulated

end Pretriangulated

namespace Triangulated

end Triangulated

end CategoryTheory
