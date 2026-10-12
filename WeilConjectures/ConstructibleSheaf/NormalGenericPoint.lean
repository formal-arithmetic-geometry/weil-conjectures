/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constant sheaves on a normal scheme and the generic point

On an integral scheme `Y` all of whose local rings are integrally closed, the constant étale
sheaf `M_Y` is the pushforward of its restriction to the generic point, and to any nonempty open
subscheme [Stacks 09Z5].

## Main statements

- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Constant sheaves on a normal scheme.** Let `Y` be an integral scheme all of whose local
rings are integrally closed, `g : Spec K ⟶ Y` the inclusion of its generic point and `M` a
`Λ`-module. Then the unit `M_Y ⟶ g_* g^* M_Y = g_* M_{Spec K}` is an isomorphism; the same
holds for the inclusion of a nonempty open subscheme.

The blueprint states this for a finite abelian group `E`; the proof (the strict henselisation
of a normal local ring is a normal domain, so the generic fibre of `Spec 𝒪ˢʰ_{Y,ȳ}` is
irreducible) applies to an arbitrary value `M`.
(blueprint: `lem-weil-pbc-normal-constant-generic`) -/
@[stacks 09Z5]
theorem Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
      ∀ {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U],
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  sorry

end AlgebraicGeometry
