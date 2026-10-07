/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
public import WeilConjectures.RingTheory.MvPolynomial.QuotientBasis
public import WeilConjectures.RingTheory.MvPolynomial.QuotientSpan

/-!
# The Hilbert functor of points of an affine space

For an affine scheme `S` and a type `n`, the Hilbert functor `Hilb^d` of the affine space
`𝔸(n; S) ⟶ S` is representable (blueprint `lem-pc-hilb-representable`, Step 4). For a family
`w` of `d` polynomials with coefficients in `R = Γ(S, ⊤)`, the subfunctor `F_w` of those `Z` for
which the images of the `w l` form a basis of `𝒪_Z` is represented by the spectrum of the
universal ring `MvPolynomial.QuotientBasisRing w`; these subfunctors are open, and they cover
`Hilb^d` since locally `𝒪_Z` has a basis of monomials.

## Main statements

- `AlgebraicGeometry.isRepresentable_hilbertPresheaf_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- **The Hilbert functor of an affine space over an affine base** (blueprint
`lem-pc-hilb-representable`, Step 4). For an affine scheme `S` and any set `n` of variables,
`Hilb^d` of the affine space `𝔸(n; S) ⟶ S` is representable. It is glued from the affine
schemes representing the subfunctors `F_W`, for `W` a set of `d` polynomials, of those `Z` for
which the images of the elements of `W` form a basis of `𝒪_Z`; these subfunctors are open and
cover `Hilb^d`. -/
theorem isRepresentable_hilbertPresheaf_affineSpace (n : Type u) (S : Scheme.{u}) [IsAffine S]
    (d : ℕ) : (hilbertPresheaf (𝔸(n; S) ↘ S) d).IsRepresentable :=
  sorry

end AlgebraicGeometry
