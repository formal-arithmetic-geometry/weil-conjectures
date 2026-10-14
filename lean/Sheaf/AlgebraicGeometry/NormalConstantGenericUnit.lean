module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Generic-point unit for a constant sheaf on an integrally closed integral scheme

This is the generic-point conjunct of Stacks Project Tag 09Z5, separated from the
normal-constant theorem so that the remaining geometric argument can be proved independently.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The unit from a constant sheaf to its generic-point pushforward is an isomorphism.
Source: Stacks Project, Tag 09Z5, generic-point part.
(blueprint: lem-weil-pbc-normal-constant-generic-unit)

Proof: evaluate the unit at an arbitrary geometric point and use the strict-henselization
stalk formula for the direct image. The strict henselization of the normal local domain at that
point is again a normal domain, and the fibre over the generic point is a nonempty localization
of it, hence is connected. Sections of a constant sheaf on this connected fibre are therefore
one copy of the coefficient module. Under the canonical pullback comparison, the stalk map of
the unit sends a coefficient to the same constant section, so it is an isomorphism. Geometric
stalks are conservative, which proves that the unit itself is an isomorphism.
-/
theorem isIso_unit_constantSheaf_generic_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  sorry

end AlgebraicGeometry.Etale
