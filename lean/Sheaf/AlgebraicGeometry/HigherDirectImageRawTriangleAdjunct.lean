module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

import Sheaf.AlgebraicGeometry.EtalePullbackSingleComp
public import Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Passing raw triangle pullback through the derived adjunction gives the mate
of the pullback-composition comparison at the shifted coefficient objects.

Proof: invert the pullback/single-functor comparison from upperStarPlusComp_single
and compose it with the raw pullback formula. Naturality of the left-adjoint
comparison moves an adjunct through this composite. Applying the inverse
adjunction equivalence reduces the equality to naturality and the counit identity.
This calculation precedes applying any homology functor, so it is only the
adjunction part of the raw-transition/toHom comparison.
Source: Stacks Project Tags 03Q8 and 09Z1; upperStarPlusComp_single and Mathlib
Adjunction.homEquiv_naturality_left_symm.
(blueprint: sbc-lem-module-raw-triangle-adjunct). -/
theorem higherDirectImageRawTrianglePullback_adjunct
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)).homEquiv _ _
      (((((a ≫ h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫
        higherDirectImageRawTrianglePullback Λ a h (a ≫ h) rfl q K K' v U z) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).homEquiv _ _
      (((((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((freeSheaf Λ S).obj U)) ≫ z) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus.transitionThrough
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (a ≫ h)).derivedPlus
        D+((a)^*[ModuleCat.{u + 1} Λ])
        (upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom (K⟦q⟧) (K'⟦q⟧)
        ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
          (shiftFunctor _ q).map v)  := by
  sorry

end AlgebraicGeometry.Etale
