/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData

/-! # Global constructible and etale-local free lattice choices -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Existence of global constructible and etale-local free lattices in a normalized presentation.
Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.4(6).

Proof: finite type over the field makes X noetherian and finite dimensional; l is a unit
because it differs from the characteristic. Apply the constructible integral lattice
lemma to L in continuous coefficients. Transport its lattice through the normalized
completion isomorphism. The finite-stratum finitely-presented condition transports to
Constructible, and associativity of scalar extension gives alpha. Independently apply
the etale-local lattice theorem, transporting coefficients to a small model when needed:
finite dimension over the small field Q_l gives a small field model of E by transport
along a basis equivalence; transport its valuation ring, uniformizer and the module
sheaves along the resulting coefficient algebra isomorphisms, apply the small-field
statement, and transport the lattices and their tensor isomorphisms back. These
transports preserve local bases and cover index universes. Refine its covering sieve
on the quasi-compact final
object by finitely many affine etale charts. Each refined chart factors through an
original lattice chart; restrict its lattice and its scalar-extension isomorphism.
Slice normalization identifies inverse image with restriction and fixes the completed
and localized coefficients by their residue projections and localization units. This
gives beta in the displayed presentation and preserves finite local freeness. The
refined charts are affine and locally of finite type over a noetherian base, hence
noetherian; their open subsets are quasi-compact, so their maps to X are quasi-compact.
Bundle N, alpha and the charts with M and beta into Choice. The empty scheme admits
the empty cover; finite free ranks may be zero or vary; N need not be globally free.
(blueprint: lem-tw-lisse-lattice-choice-existence). -/
theorem lattice_choice_exists (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (a : Realizations l E) (X : LisseRealization.Base D l hl)
    (L : RationalModules l E X.scheme) (hL : L.IsFiniteLocallyFree) :
    Nonempty (Choice l E a X.scheme L) := by sorry

end WeilConjectures.LisseLattice
