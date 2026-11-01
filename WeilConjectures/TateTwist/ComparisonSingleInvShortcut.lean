/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.TateTwist.ComparisonSingleInv

/-!
# The inverse of `Rν_* ν^* S ≅ S`, with the shortcut instance

`AlgebraicGeometry.ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso_inv'`: the statement of
`rightDerivedComparisonLowerStarSingleFunctorIso_inv` elaborated on the shortcut instance
`ModuleCat.isGrothendieckAbelian_of_commRing` (whereas
`rightDerivedComparisonLowerStarSingleFunctorIso`
is built on the Mathlib instance `IsGrothendieckAbelian (ModuleCat Λ)`). Comparing the two instances
directly is costly in the kernel; here the comparison is done once, on a small statement.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- `rightDerivedComparisonLowerStarSingleFunctorIso_inv`, with the shortcut instance
`ModuleCat.isGrothendieckAbelian_of_commRing` in the right-hand side. -/
lemma rightDerivedComparisonLowerStarSingleFunctorIso_inv' (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S).inv =
      (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app _ ≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).hom.app S) := by
  generalize ModuleCat.isGrothendieckAbelian_of_commRing Λ = i
  obtain rfl := Subsingleton.elim i (@instIsGrothendieckAbelianModuleCat Λ _)
  exact rightDerivedComparisonLowerStarSingleFunctorIso_inv Λ X S

end AlgebraicGeometry.ProEtale
