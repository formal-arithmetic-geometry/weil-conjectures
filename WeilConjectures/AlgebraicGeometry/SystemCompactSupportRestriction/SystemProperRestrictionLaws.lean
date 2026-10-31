/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestriction.SystemCompactSupportRestrictionData

/-! # Coherence laws for proper restriction comparisons

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y.
(blueprint: lem-sp-system-proper-restriction-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

/-- Normalized proper comparisons obey composition and identity laws.

Source: Stacks, sites-cohomology.tex, Tag 0D6E; derived.tex, Tag 070Y.
Proof: choose successive K-injective resolutions and apply naturality of the
three normalized comparisons.  The resolution maps are quasi-isomorphisms and
cancel in the derived category, so the two composite comparison words agree.
For an identity coefficient map use the identity resolution on K-injectives;
the normalization reduces to the derived unitor equation.  Every derived object
is isomorphic to a localized K-injective representative, and naturality
transports both equations to all objects. -/
theorem systemProperRestrictionLaws (l : ℕ) [Fact l.Prime]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (c : RestrictionIdentifications.{u} l)
    (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
      (a : B.rings ⟶ C.rings), GeometricSquare a p)
    (q : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l)
      (a : B.rings ⟶ C.rings), ProperComparison (g B C a)) :
    (∀ (B C D : Etale.SystemProjection.Coefficients.{u} l)
      (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
      (M : VaryingRing.Derived (levels D) (steps D) Z),
      (VaryingRing.P (levels B) (steps B) p).map ((c.rho Z a b).hom.app M) ≫
          (q B D (a ≫ b)).iso.hom.app M =
        (q B C a).iso.hom.app ((derivedRestriction Z b).obj M) ≫
          (derivedRestriction Y a).map ((q C D b).iso.hom.app M) ≫
          (c.rho Y a b).hom.app
            ((VaryingRing.P (levels D) (steps D) p).obj M)) ∧
    (∀ (B : Etale.SystemProjection.Coefficients.{u} l)
      (M : VaryingRing.Derived (levels B) (steps B) Z),
      (q B B (𝟙 B.rings)).iso.hom.app M ≫
          (c.derivedUnit Y B).hom.app
            ((VaryingRing.P (levels B) (steps B) p).obj M) =
        (VaryingRing.P (levels B) (steps B) p).map
          ((c.derivedUnit Z B).hom.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
