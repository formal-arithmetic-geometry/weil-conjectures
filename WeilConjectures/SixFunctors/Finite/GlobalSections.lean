/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Finite.Exact

/-!

# Cohomology of a finite pushforward

For a finite morphism `π : X ⟶ Y` the pushforward `π_*` on étale sheaves is exact, so its
right derived functor is `π_*` applied levelwise
(`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`), and the Leray
isomorphism `RΓ(Y, Rπ_* K) ≅ RΓ(X, K)` becomes `RΓ(Y, π_* K) ≅ RΓ(X, K)`: in every degree
`H^q(Y, π_* F) ≅ H^q(X, F)`.

## Main definitions

- `AlgebraicGeometry.Etale.mapDerivedCategoryLowerStarCompRightDerivedGlobalSectionsIso`: the
  isomorphism `D(π_*) ⋙ RΓ_Y ≅ RΓ_X` for a finite `π`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π]

end AlgebraicGeometry.Etale
