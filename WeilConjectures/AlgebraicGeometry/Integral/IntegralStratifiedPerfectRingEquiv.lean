/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels

/-! # Stratified perfect models under isomorphisms of coefficient data

A ring isomorphism `φ : A ≃+* A'` carrying the ideal of one adic coefficient datum onto the
ideal of another identifies all finite quotients, hence the quotient coefficient sheaves,
their limit and the completed module categories. Every construction entering the bounded
constructible complete category and the stratified-perfect property is natural in the pair
(ring, ideal), so the implication from the former to the latter transports.

Source: Bhatt--Scholze, Proposition 6.6.11 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The implication "bounded constructible complete implies stratified perfect" is invariant
under isomorphisms of adic coefficient data.
Source: Bhatt--Scholze, Proposition 6.6.11 (auxiliary; not a blueprint node).
Proof: φ induces ring isomorphisms `A/I^(n+1) ≃ A'/I'^(n+1)` compatible with all quotient
maps, hence an isomorphism of the finite coefficient sheaves of continuous component
functions, of their quotient system and of its limit `ρ : A_T ≅ A'_T`, compatible with the
level projections and with the constant scalars. Restriction of scalars along `ρ` is an
exact equivalence of module sheaf categories, hence of derived categories, commuting with
derived reduction (by the projection compatibility), with the intrinsic completion unit,
with the strict tower normalizations and with the retained etale origins (restriction along
the level isomorphisms). Thus it carries `K` to a bounded constructible complete `K'` for
`d'`, which is stratified perfect by hypothesis. Restriction of scalars commutes with
inverse image along stratum-cover maps and slice restriction, and it identifies the ordinary
completed realization of an `A'`-module with that of its restriction along `φ`. Restriction
along `φ` preserves bounded finite-projective complexes. Transporting the local models of
`K'` back gives local models of `K` on the same strata and sieves. -/
theorem isIntegralStratifiedPerfect_of_ringEquiv (T : Scheme.{u})
    {A A' : Type (u + 1)} [CommRing A] [CommRing A']
    (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
    (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)
    (h' : ∀ K' : PbcCompletedDerived T d', PbcIsBoundedConstructibleComplete T d' K' →
      IsIntegralStratifiedPerfect T d' K')
    (K : PbcCompletedDerived T d) (hK : PbcIsBoundedConstructibleComplete T d K) :
    IsIntegralStratifiedPerfect T d K := by
  sorry

end AlgebraicGeometry.Scheme
