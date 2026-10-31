/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestrictionData

/-! # Proper restriction comparison data

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y.
(blueprint: lem-sp-system-proper-restriction-data).

The construction part of proper coefficient restriction coherence is isolated here.
The later cocycle and unit equations are stated separately so that the derived
comparison construction and its coherence can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

/-- Proper restriction supplies normalized geometric squares and comparisons.

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y.
Proof: construct the identity-on-sections ringed-topos square for each coefficient
map and take its inverse-image mate.  The two factorizations of the same proper
ringed morphism have canonically isomorphic derived direct images.  Define the
comparison by the ratio of these factorizations.  On a K-injective target and any
K-injective resolution of its restriction, the derived pushforward composition
comparison identifies this ratio with the inverse image of the resolution map;
this proves the full `ProperComparison.normalized` field, without requiring that
restriction preserve K-injectives. -/
theorem systemProperRestrictionData (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (c : RestrictionIdentifications.{u} l) :
    ∃ (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), GeometricSquare a p),
      Nonempty (∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
        (a : B.rings ⟶ C.rings), ProperComparison (g B C a)) := by
  sorry

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
