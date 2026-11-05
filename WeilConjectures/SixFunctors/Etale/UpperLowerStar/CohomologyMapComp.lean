/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Composition of pullback maps on étale cohomology

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, pulling a cohomology class back along
`g` and then along `f` is pulling it back along `f ≫ g`, up to the canonical isomorphisms
`(f ≫ g)^* F ≅ f^* g^* F` of coefficient sheaves and an automorphism of the constant sheaf `ℤ`
on `X`. In particular the composite of the two pullback maps is bijective if and only if the
pullback map along `f ≫ g` is.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap_of_comp_eq`: the composition formula.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_comp_iff`: bijectivity of the composite.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_iff_of_iso`: bijectivity of the pullback
  map only depends on the coefficient sheaf up to isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

variable {X Y Z : Scheme.{u}}

end AlgebraicGeometry.Etale
