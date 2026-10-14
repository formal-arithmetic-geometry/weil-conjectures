module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Open-subscheme unit for a constant sheaf on an integrally closed integral scheme

This is the nonempty-open conjunct of Stacks Project Tag 09Z5, separated from the generic-point
argument so it can be developed independently.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The unit to the pushforward from every nonempty open subscheme is an isomorphism.
Source: Stacks Project, Tag 09Z5, nonempty-open part.
(blueprint: lem-weil-pbc-normal-constant-generic-open-unit)

Proof: a nonempty open subscheme of an integral scheme contains its generic point and has the
same function field. Factor the generic-point map through this open immersion. The strict
henselization calculation from the generic-point case applies unchanged: its generic fibre is a
nonempty localization of a normal domain and is connected, so constant sections are exactly one
copy of the coefficient module. The direct-image composition comparison identifies the open
unit followed by the generic-point unit with the generic-point unit for the original scheme.
Both generic-point units are isomorphisms, and the comparison is an isomorphism, so the open unit
is an isomorphism; conservativity of geometric stalks completes the sheaf argument.
-/
theorem isIso_unit_constantSheaf_open_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    [Nonempty U] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  sorry

end AlgebraicGeometry.Etale
