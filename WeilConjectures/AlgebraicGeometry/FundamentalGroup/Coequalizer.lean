/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCategory
public import WeilConjectures.CategoryTheory.Limits.CoequalizerOfQuotient

/-!
# Finite colimits of finite étale schemes

Let `Y` be a scheme. The category `FÉt(Y)` of finite étale `Y`-schemes has coequalizers, hence
all finite colimits (blueprint `lem-fet-finite-limits`).

The coequalizer of `f g : Z ⟶ P` is the quotient of `P ⨿ Z` by the action of the finite monoid
`{1, l, r}` (`CategoryTheory.Limits.ParallelPairMonoid`) in which `l` and `r` act by
`𝟙 P ⨿ f` and `𝟙 P ⨿ g`
(`CategoryTheory.Limits.hasCoequalizers_of_hasColimitsOfShape_singleObj`).
Quotients of finite étale `Y`-schemes by finite monoid actions exist by
`AlgebraicGeometry.Scheme.FiniteEtale.hasColimitsOfShape_singleObj`: they are glued from the
spectra of the rings of invariants over the affine opens of `Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-- **`FÉt(Y)` has coequalizers** (blueprint `lem-fet-finite-limits`): the coequalizer of
`f g : Z ⟶ P` is the quotient of `P ⨿ Z` by a finite monoid action. -/
instance : HasCoequalizers Y.FiniteEtale :=
  have := hasColimitsOfShape_singleObj Y ParallelPairMonoid.{u}
  hasCoequalizers_of_hasColimitsOfShape_singleObj.{u}

/-- **`FÉt(Y)` has finite colimits** (blueprint `lem-fet-finite-limits`). -/
instance : HasFiniteColimits Y.FiniteEtale :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end AlgebraicGeometry.Scheme.FiniteEtale
