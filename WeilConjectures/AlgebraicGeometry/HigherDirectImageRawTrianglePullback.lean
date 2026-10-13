/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-! # Raw pullback for a commutative triangle

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Pullback of a derived class, followed by a specified coefficient morphism. The
coefficient morphism is given data, and no witness is chosen from an existence theorem. -/
noncomputable def higherDirectImageRawTrianglePullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h' q K').obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app _) ≫
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[ModuleCat.{u + 1} Λ]).map z ≫
    (D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
    (shiftFunctor _ q).map v

/-- Restriction naturality of the raw pullback.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
Proof: Naturality of restriction through each displayed pullback factor, followed by
functoriality and associativity. -/
theorem higherDirectImageRawTrianglePullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K')
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U))
    (T : S.Etale) (b : T ⟶ U) :
    higherDirectImageRawTrianglePullback Λ a h h' w q K K' v T
        ((higherDirectImagePresheaf Λ h q K).map b.op z) =
      (higherDirectImagePresheaf Λ h' q K').map b.op
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U z):= by
  sorry

end AlgebraicGeometry.Etale
