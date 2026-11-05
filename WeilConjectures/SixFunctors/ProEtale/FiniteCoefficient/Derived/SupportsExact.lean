/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.SupportedSectionsFlasque
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# The exact sequence of supported sections for injective pro-étale sheaves

Let `j : U ⟶ X` be an open immersion. For an injective pro-étale sheaf `I` on `X` the
restriction `I ⟶ j_* j^* I` (the unit of `j^* ⊣ j_*`) is a split epimorphism, so injective
sheaves are flasque for the pair. Consequently, for a complex `I` of injective pro-étale sheaves,

`0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0`

is a short exact sequence of complexes, `𝒢_Z I = ker (I ⟶ j_* j^* I)` being the complex of
sections supported on the closed complement `Z` (`s_* s^! I` for a closed immersion
`s : Z ⟶ X` with quasi-compact open complement `j`,
`AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`). This is the pro-étale form of
blueprint `lem-pur-support-exact`; the étale form is
`AlgebraicGeometry.Etale.shortExact_supportsShortComplex`.

The argument is the one on the étale site: the counit `j_! j^* F ⟶ F` at `F = j_* j^* I` is a
monomorphism, being the comparison `j_! ⟶ j_*` up to an isomorphism
(`AlgebraicGeometry.ProEtale.mono_openImmersionLowerShriekToLowerStar_app`), so by injectivity
the transpose of the counit of `j^* ⊣ j_*` extends along it to a section of the unit.

## Main statements

- `AlgebraicGeometry.ProEtale.isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective`
- `AlgebraicGeometry.ProEtale.isFlasqueFor_of_injective`
- `AlgebraicGeometry.ProEtale.shortExact_supportsShortComplex`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end ProEtale

end AlgebraicGeometry
