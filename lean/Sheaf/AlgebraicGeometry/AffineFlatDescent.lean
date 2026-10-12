/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# The affine case of effective descent

Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245), affine case.
(blueprint: lem-galois-affine-flat-descent-effective).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- Descent of an affine morphism along a flat surjective map of affine schemes.

Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245), the affine case in its proof.
Write the base, cover and total space as `Spec R`, `Spec A` and `Spec B`; the last
is affine because its morphism to the affine cover is affine. The descent isomorphism
is, contravariantly, an isomorphism `B ⊗[R] A ≃ A ⊗[R] B`. Evaluating at `b ⊗ 1`
gives an `A`-algebra coaction. The threefold cocycle gives coassociativity; restriction
of the cocycle to the diagonal gives an invertible idempotent endomorphism of `B`,
hence the identity, which is the counit. Flat algebra descent gives the invariant
`R`-algebra `C` and the isomorphism `A ⊗[R] C ≃ₐ[A] B`, sending `a ⊗ c` to `ac`.
Its spectrum yields the pullback square over `Spec R`. Compatibility with transport
is checked on the invariant generators `c ⊗ 1`: both composites send these to
`1 ⊗ 1 ⊗ c`, and these generate because the comparison isomorphism is surjective.
Transporting the resulting square through the initial affine identifications proves
effectivity for the original schemes. The flat algebra theorem used here is
`Algebra.DescentDatum.descendedEquiv`; it requires only flatness. Surjectivity is
retained to match the affine case in the fpqc reduction.

(blueprint: lem-galois-affine-flat-descent-effective) -/
theorem isEffective_of_isAffineHom_flat_affine {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) (hf : Flat f) (hs : Surjective f)
    {V : Over X} [IsAffineHom V.hom] (D : Over.DescentDatum f V) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
