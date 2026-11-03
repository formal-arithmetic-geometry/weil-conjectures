/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldFiniteDualizingComponents

/-! # Finite dualizing scalar and site compatibility
(blueprint: lem-sf-general-field-finite-dualizing-scalar-site). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The specified finite pro-etale scalar maps obey the tensor-unit, compact-support
site, counit, and coefficient-composition equations.

Source: latest blueprint, `lem-coef-finite-dualizing.proof.md`, paragraph 3,
and `lem-coef-finite-free-extension.proof.md`, coefficient compatibility paragraph.
(blueprint: lem-sf-general-field-finite-dualizing-scalar-site).

Proof: represent scalar extension by its actual adjunction with exact restriction.
The sectionwise restriction/coextension identity has inverse mate delta. Compare
the proper scalar mates by the scalar/site/pullback cube, and the open scalar
maps by their open-adjunction units. Paste these squares at the same
compactification. The ordinary compact scalar comparison equals the specified
etaleGamma/open composite because their restriction transposes and their open
unit transposes agree. Thus the paste is the displayed mixed square for the
actual generalFieldFiniteProCompactMap, rather than merely an isomorphism of its
endpoints. On bounded constructible finite-Tor inputs the scalar extension is
bounded below; the site components, delta, and ordinary compact scalar map are
invertible. Cancellation in the mixed square gives invertibility of its pro-etale
component. Apply the square at the dualizing object using its constructibility
and finite Tor amplitude, substitute the ordinary coefficient-counit equation,
and move delta past the counit by naturality. The finite compactification
transpose formula for epsilon gives the asserted pro-etale counit equation.
For two coefficient maps, exact restriction composition and the inverse-mate
pasting law identify the composite deltas with the delta of the composite,
under the specified scalar associators. Transport the ordinary dualizing cocycle
through that equality and delta naturality to obtain pro_site_composition.
For the identity coefficient map the restriction comparison is the identity
square; its inverse mate is the canonical scalar unit. Transporting the ordinary
identity counit mate gives pro_identity. These arguments use arbitrary finite
ell-primary rings, including nonflat quotient maps. -/
theorem generalFieldFiniteDualizingScalarSite
    (k : Type u) [Field k] (p l : ℕ) (hp : p.Prime) (hkp : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l.Prime) (hlp : l ≠ p)
    {X : Scheme.{u}} {a : X ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0) (φ : A →+* B) :
    GeneralFieldFiniteDualizingScalarSite l φ a := by
  sorry

end AlgebraicGeometry.Etale
