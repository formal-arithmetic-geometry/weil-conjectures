/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.ComparisonSingle

/-!
# The inverse of `Rν_* ν^* S ≅ S`

The inverse of `AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso` is the
unit of the comparison adjunction followed by `Rν_*` of `D(ν^*)(S[0]) ≅ (ν^* S)[0]`
(`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso_inv`). It is stated
here, in the instance context of the definition, so that its kernel check does not compare
different spellings of the instances.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The inverse of `Rν_* ν^* S ≅ S` is the unit `S[0] ⟶ Rν_* ν^* (S[0])` followed by `Rν_*` of
`ν^*(S[0]) ≅ (ν^* S)[0]`. -/
lemma rightDerivedComparisonLowerStarSingleFunctorIso_inv (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S).inv =
      (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app _ ≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app S) :=
  rfl

end AlgebraicGeometry.ProEtale
