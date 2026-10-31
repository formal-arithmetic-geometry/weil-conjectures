/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedReductionTransportData

/-! # Numerical weights and filtrations under a locally compatible Weil equivalence

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, final paragraph; parent proof steps 9--10.
(blueprint: lem-zl-condensed-reduction-numerical-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedReduction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- A specified exact Weil equivalence with the canonical local Frobenius comparisons
preserves and reflects numerical weights and transports every finite pure filtration.
The equivalence and its local compatibility are hypotheses: this is the numerical
and cokernel argument, independent of the construction of the reduction equivalence.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, final paragraph;
Deligne, Weil II, (1.2); parent proof steps 9--10.
(blueprint: lem-zl-condensed-reduction-numerical-transport).

Proof:
1. For a closed point of the reduction the residue-field isomorphism bijects compatible
embeddings in the chosen algebraic closure. For an arbitrary closed point of the
original scheme use the closed-point equivalence in LocalCompatibility to obtain the
unique such point. The residue-field composition identity shows that compatible
embeddings correspond in both directions; the residue cardinalities are unchanged.
2. The two specified fibre isomorphisms intertwine the local operators. They carry
eigenvectors, with the same eigenvalue, in both directions, so each punctual pure weight
is preserved and reflected. Transport any finite basis through the linear isomorphism:
the matrices of the local operators coincide. Their reverse characteristic polynomials
have identical coefficients. Thus the reality conditions agree for every specified
basis and residue embedding. This also handles zero-dimensional fibres.
3. The full constructible Weil subcategories are closed under kernels and cokernels:
forget the Weil structure, use coefficientHeart, and use exact Frobenius pullback to
induce the invertible structure on each universal kernel and cokernel. The inclusions
therefore preserve these universal properties. Restrict an ambient cokernel cofork to
the heart, apply either exact equivalence, and include it in the target ambient Weil
category. Its colimit property is preserved. The resulting quotient is the image of
the specified constructible quotient, and step 2 preserves its assigned pure weight.
4. Apply the exact functor to every term and arrow of any prescribed finite filtration.
It preserves zero objects and monomorphisms, and step 3 gives PureQuotient for each
successive arrow at the same weight. Unique cokernel isomorphisms identify these
quotients with the chosen ambient cokernels in the definition of Mixed; step 2 makes
purity invariant under these isomorphisms. The resulting chain and its identity endpoint
isomorphism witness Mixed with the same upper bound. This proves ImageFiltrations in
both directions, including repeated terms and length zero.
5. For any Mixed witness, regard its sequence of adjacent monomorphisms as a finite
functor to the heart. Apply step 4 and compose its endpoint isomorphism with the
functorial image of the original endpoint isomorphism. This proves preservation of
Mixed. Apply the inverse equivalence and the actual unit or counit for reflection.
Combine with step 2 to obtain NumericalCompatibility for both functors. -/
theorem reduction_numerical_transport (hl : l ≠ D.p) [IsSeparated X₀.hom]
    {h : Commutes D X₀} (E : WeilEquivalence D l X₀ h)
    (hlocal : LocalCompatibility D l X₀ E) (iota : PadicAlgCl l ≃+* ℂ) :
    NumericalCompatibility D l X₀ E iota ∧
      ImageFiltrations D l X₀ (model X₀) E.inverseImage iota.toRingHom ∧
      ImageFiltrations D l (model X₀) X₀ E.directImage iota.toRingHom := by
  sorry

end WeilConjectures.CondensedReduction
