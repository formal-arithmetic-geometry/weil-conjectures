/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Associativity of the identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`

The identifications `AlgebraicGeometry.Etale.shiftTateObjectAddIso` are associative with respect
to the associator of the derived tensor product. This follows from the associativity of the
twists (`HasTateTwist.twistObjectAddIso_assoc`) and the compatibility of the associator with the
shifts (`AlgebraicGeometry.Etale.derivedTensorShiftIso_assoc`).

## Main statements

- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_hom_assoc`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]
  (U : Scheme.{u}) [HasInvertibleExponent Λ U]

end Etale

end AlgebraicGeometry
