/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Direct sums and finite cohomological dimension

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension and a torsion
ring `Λ`, the derived pushforward `Rf_*` on unbounded derived categories of étale sheaves of
`Λ`-modules commutes with direct sums, and similarly for `RΓ(X, -)` (blueprint `lem-kun-0f11`,
Stacks 0F11).

## Main statements

- `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar` and
  `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedGlobalSections` (`lem-kun-0f11`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-0f11`: direct sums and finite cohomological dimension.

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension and a torsion
ring `Λ`, `Rf_* : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedLowerStar (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : HasFiniteCohomologicalDimensionMorphism Λ f) (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (R((f)_*[ModuleCat.{u + 1} Λ])) :=
  sorry

/-- Blueprint `lem-kun-0f11`, part (2): for a quasi-compact quasi-separated scheme `X` of finite
cohomological dimension and a torsion ring `Λ`, `RΓ(X, -)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedGlobalSections (hΛ : IsAddTorsion Λ) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasFiniteCohomologicalDimension Λ X)
    (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) :=
  sorry

end Etale

end AlgebraicGeometry
