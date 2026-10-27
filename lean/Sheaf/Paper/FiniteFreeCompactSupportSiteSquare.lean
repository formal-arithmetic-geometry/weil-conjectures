/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.Paper.FiniteFreeCompactSupportData

/-! # Canonical finite-free compact-support squares

Source: current blueprint sk-thm-purity-transport, Steps 1, 3 and 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
namespace AlgebraicGeometry.FiniteFreeCompactSupport

/-- The mixed scalar/site square for the actual compact-support coefficient arrow.
Source: current blueprint sk-thm-purity-transport, Steps 1, 3 and 4; node
lem-pur-topos-compact-scalar-site-pasting, proof Steps 1--5
(blueprint: lem-pur-finite-free-compact-site-square).

Proof: present the small etale and pro-etale sites as the two systems of that
pasting lemma. The scalar/inverse-image cube is the canonical scalar pullback
cube. Take proper right mates using the fixed direct-image counits and open
left mates using the open units. The former is the actual scalarMate and the
latter is openIso. The scalar transpose of their restriction paste is exactly
the definition of coefficientMap true. Paste the two mixed squares, obtaining
the square at the scalar extension of L. Transport its B-input along gamma by
naturality of the proper/open site comparison. The two occurrences of gamma
cancel. This is the displayed SiteCompatibility equation, with every arrow
still B-linear. Finite freeness gives termwise scalar representatives; it does
not assert faithfulness of scalar restriction or site pullback. -/
theorem finiteFree_site_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hφ : letI := φ.toAlgebra; Module.Finite A B ∧ Module.Free A B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (γ : N.obj ≅ (Sites.scalar false φ X).obj L.obj) :
    SiteCompatibility φ c L N γ := by sorry

end AlgebraicGeometry.FiniteFreeCompactSupport
