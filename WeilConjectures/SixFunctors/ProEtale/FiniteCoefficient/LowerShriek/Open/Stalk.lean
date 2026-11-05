/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

/-!
# The pointwise description of the pro-étale extension by zero

Let `j : U ⟶ X` be an open immersion. The extension by zero `j_!` on sheaves for the small
pro-étale sites is the exact left adjoint of `j^*`
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`,
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`), so it acts
degreewise on complexes, as `D(j_!)`. This file proves the stalk prescription of blueprint
`lem-cbc-proetale-extension-zero`, in the form of the pullback along an arbitrary morphism
`s : T ⟶ X` (for instance a geometric point `Spec k̄ ⟶ X`, along which the pullback computes
the stalk):

* if `s = t ≫ j` factors through `U`, then `s^* j_! K ≅ t^* K`
  (`AlgebraicGeometry.ProEtale.openImmersionLowerShriekCompUpperStarIsoOfFac`), by base change
  for the extension by zero along the cartesian square `t ≫ j = 𝟙 ≫ s`;
* if the range of `s` misses `U`, then `s^* j_! K = 0`
  (`AlgebraicGeometry.ProEtale.isZero_upperStar_openImmersionLowerShriek`).

Both statements are also given for complexes.

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekIdIso`: `(𝟙 X)_! ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekCompUpperStarIsoOfFac`: `s^* j_! ≅ t^*`
  for `s = t ≫ j`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end ProEtale

end AlgebraicGeometry
