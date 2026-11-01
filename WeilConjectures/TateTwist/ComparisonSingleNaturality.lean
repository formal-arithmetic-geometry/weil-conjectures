/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.ComparisonSingleRestrictScalars

/-!
# `Rν_* ν^* S ≅ S` is natural in the sheaf `S`

`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso_hom_comp_map`: the
instance of `CategoryTheory.Adjunction.iso_hom_comp_eq_map_comp_iso_hom`. It has a file of its own
because of its kernel cost.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

-- The instance `IsGrothendieckAbelian (ModuleCat Λ)` of the definition of
-- `rightDerivedComparisonLowerStarSingleFunctorIso`.
attribute [local instance 20000] instIsGrothendieckAbelianModuleCat

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- The naturality of `Rν_* ν^* S ≅ S` (`rightDerivedComparisonLowerStarSingleFunctorIso`) in the
sheaf `S` (stated as `rightDerivedComparisonLowerStarSingleFunctorIso_hom_naturality`). -/
lemma rightDerivedComparisonLowerStarSingleFunctorIso_hom_comp_map
    {S T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : S ⟶ T) :
    (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S).hom ≫
        (DerivedCategory.singleFunctor _ 0).map g =
      (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          ((DerivedCategory.singleFunctor _ 0).map (ν^*(X)[ModuleCat.{u + 1} Λ].map g)) ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ X T).hom :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).iso_hom_comp_eq_map_comp_iso_hom _ _
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app S)
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app T)
    (rightDerivedComparisonLowerStarSingleFunctorIso_inv Λ X S)
    (rightDerivedComparisonLowerStarSingleFunctorIso_inv Λ X T) _ _
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.naturality g)

end AlgebraicGeometry.ProEtale
