/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.ComparisonSingleInvShortcut
public import WeilConjectures.TateTwist.ComparisonSingleRestrictScalars

/-!
# `Rν_* ν^* S ≅ S` commutes with the restriction of scalars

`ProEtale.derivedRestrictScalars_map_rightDerivedComparisonLowerStarSingleFunctorIso_hom_eq`:
the instance of `CategoryTheory.map_iso_hom_eq_mateEquiv_app_comp`, through
`rightDerivedComparisonLowerStarSingleFunctorIso_inv'`. It has a file of its own because of its
kernel cost.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- `Rν_* ν^* S ≅ S` commutes with the restriction of scalars (stated as
`derivedRestrictScalars_map_rightDerivedComparisonLowerStarSingleFunctorIso_hom`). -/
lemma derivedRestrictScalars_map_rightDerivedComparisonLowerStarSingleFunctorIso_hom_eq
    (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ' X S).hom =
      (derivedRestrictScalarsCompComparisonLowerStarMap φ X).app
          ((DerivedCategory.singleFunctor _ 0).obj (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S)) ≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
              0).hom.app (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S) ≫
            (DerivedCategory.singleFunctor _ 0).map
              ((asIso (restrictScalarsCompComparisonUpperStar φ X)).inv.app S)) ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ X
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj S)).hom ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
          0).inv.app S :=
  map_iso_hom_eq_mateEquiv_app_comp (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X) _ _
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom _ _
    (((ν^*(X)[ModuleCat.{u + 1} Λ']).mapDerivedCategorySingleFunctor 0).hom.app S)
    (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj S))
    (rightDerivedComparisonLowerStarSingleFunctorIso_inv' Λ' X S)
    (rightDerivedComparisonLowerStarSingleFunctorIso_inv' Λ X _)
    (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).app S) _
    (map_mapDerivedCategorySingleFunctor_hom_app_comp_restrictScalars φ X S)

end AlgebraicGeometry.ProEtale
