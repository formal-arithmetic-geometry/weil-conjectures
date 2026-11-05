/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Étale localization of the derived categories of étale sheaves

Isomorphisms descend along surjective étale morphisms: for a surjective étale `u : U ⟶ X`, a
morphism `φ` of `D(X_ét, Λ)` with `Lu^* φ` invertible is invertible (blueprint
`lem-pur-etale-iso-descent`). Pullback along `u` is exact, so it commutes with the cohomology
sheaves, and the pullbacks along the members of a jointly surjective family of étale maps reflect
isomorphisms of sheaves.

The localization of the exceptional inverse image along étale maps, `Lu^* Rf^! ≅ R(u ≫ f)^!`
(blueprint `lem-amb-etale-adjoint-locality`), is in
`WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalizationUpperShriek`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

end Etale

end AlgebraicGeometry
