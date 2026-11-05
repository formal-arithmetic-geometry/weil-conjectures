/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# Étale localization of the exceptional inverse image

For an étale morphism `u : U ⟶ X` and `f : X ⟶ Y` admitting compactifications, the exceptional
inverse image localizes along `u`: `Lu^* Rf^! ≅ R(u ≫ f)^!` (blueprint
`lem-amb-etale-adjoint-locality`, a node of the blueprint subsection `sk-prop-sf-cbc`).

The extension by zero `u_!` is left adjoint to `u^*`, and its derived functor `De_!` agrees with
the derived lower shriek `Ru_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`).
So `Ru_! ⊣ Lu^*`, and composing with `Rf_! ⊣ Rf^!` and `R(u ≫ f)_! ≅ Ru_! ⋙ Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) gives the isomorphism by
uniqueness of right adjoints.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Etale

end AlgebraicGeometry
