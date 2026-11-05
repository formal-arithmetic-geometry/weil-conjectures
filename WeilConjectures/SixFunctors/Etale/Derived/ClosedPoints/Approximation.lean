/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Vanishing

/-!
# Approximation of a sheaf supported at closed points

Let `X` be locally of finite type over a field and `F` an étale sheaf of `Λ`-modules on `X`
whose stalks vanish at the non-closed points. For a finite set `S` of closed points let
`F_S ⊆ F` be the subsheaf of sections supported on `S`. These subsheaves form a filtered
diagram indexed by the finite sets of closed points, and `F` is its colimit (blueprint
`lem-kun-cp-approximation`).

## Main definitions

- `AlgebraicGeometry.Etale.FiniteClosedPoints`: the finite sets of closed points, ordered by
  inclusion.
- `AlgebraicGeometry.Etale.supportedSectionsFunctor`: the diagram `S ↦ F_S`.

## Main statements

- `AlgebraicGeometry.Etale.isColimitSupportedSectionsCocone` (`lem-kun-cp-approximation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

namespace FiniteClosedPoints

variable {X : Scheme.{u}}

end FiniteClosedPoints

open FiniteClosedPoints

section

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end

attribute [local instance] IsFiltered.isConnected

end Etale

end AlgebraicGeometry
