/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionProjection

/-!
# The sheaf `S_X` is of étale origin

The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét`
(`AlgebraicGeometry.ProEtale.sheafRestrictScalarsUnit`) is the constant sheaf with value `S`,
hence the pro-étale realization `ν^*` of an étale sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

/-- The sheaf `S_X` of `R`-modules underlying the unit sheaf of `S`-modules on `X_proét` is of
étale origin. -/
theorem exists_comparisonUpperStar_obj_iso_sheafRestrictScalarsUnit (X : Scheme.{u}) :
    ∃ c₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R),
      Nonempty ((ν^*(X)[ModuleCat.{u + 1} R]).obj c₀ ≅ sheafRestrictScalarsUnit R S X) :=
  sorry

end AlgebraicGeometry.ProEtale
