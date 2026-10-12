/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Height from homogeneous independence at a rational point

Source: the invariant-derivation argument in Waterhouse, *Introduction to Affine Group
Schemes*, §11.4, as recorded in `WeilConjectures.RingTheory.HopfAlgebra.Cartier`, and the
local dimension step of blueprint `lem-wf-same-lie-closed-subgroup`, clause (2).
(blueprint: lem-wf-height-of-homogeneous-independence).
-/

@[expose] public section

open MvPolynomial

namespace AlgHom

/-- A polynomial associated graded ring has local dimension the number of its variables.

Source: the local dimension step of `lem-wf-same-lie-closed-subgroup`, clause (2), with
regularity obtained from the homogeneous independence argument recorded in
`WeilConjectures.RingTheory.HopfAlgebra.Cartier` (Waterhouse, §11.4).

Proof in words: put `I = ker ε`. The map `ε` is onto, since it is a `k`-algebra map to
`k`, and identifies `A/I` with `k`. The spanning hypothesis implies, by induction on
`r` using products of elements of `I`, that every class in `I^r/I^(r+1)` is the value
of a homogeneous degree-`r` polynomial in the `xᵢ`. Its kernel is zero by the second
hypothesis. Multiplication respects these maps, so they give an isomorphism of graded
`k`-algebras from `k[Xᵢ]` to the associated graded algebra of `I`.

Localize at `I`. Every `I^r/I^(r+1)` is annihilated by `I`, hence is a `k`-vector space;
elements outside `I` act by a nonzero scalar, so localization changes none of these
quotients. Thus the local ring `A_I` has this same polynomial associated graded algebra.
Write `n` for the number of variables. The classes of the `xᵢ` generate the maximal
ideal modulo its square, so Nakayama makes their images generators of the maximal
ideal. Krull intersection makes this local ring separated for that ideal. If `n=0`,
Nakayama makes the maximal ideal zero, so the local ring is a field of dimension zero.
Otherwise choose `x₁`. Every nonzero element has finite adic order, and multiplication
by `x₁` increases its order by exactly one, because multiplication by `X₁` is injective
on the polynomial associated graded ring. Thus `x₁` is a nonzerodivisor and
`(x₁) ∩ m^r = x₁ m^(r-1)` for `r ≥ 1`. This strictness identifies the associated graded
ring of the quotient by `x₁` with `k[Xᵢ]/(X₁)`, a polynomial ring on `n-1` variables.
Induction gives dimension `n-1` for this quotient. The dimension-drop theorem for a
nonzerodivisor in the maximal ideal of a Noetherian local ring gives dimension `n`
for the local ring. This theorem is
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` in Mathlib. Finally the
dimension of `A_I` is the height of `I`, giving the asserted equality.
(blueprint: lem-wf-height-of-homogeneous-independence). -/
theorem height_ker_eq_card_of_homogeneous_independence
    {k A ι : Type*} [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    [Fintype ι] (ε : A →ₐ[k] k) (x : ι → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ a ∈ RingHom.ker ε, ∃ c : ι → k,
      a - ∑ i, algebraMap k A (c i) * x i ∈ RingHom.ker ε ^ 2)
    (hind : ∀ (r : ℕ) (f : MvPolynomial ι k), f.IsHomogeneous r →
      aeval x f ∈ RingHom.ker ε ^ (r + 1) → f = 0) :
    (RingHom.ker ε).height = Fintype.card ι := by sorry

end AlgHom
