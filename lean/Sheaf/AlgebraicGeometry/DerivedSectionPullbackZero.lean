/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Degree-zero derived section pullback

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-derived-section-pullback-zero).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Degree-zero derived section pullback before any restriction-triangle comparison.
Source: Stacks Project, Tag 07A6, derived adjunction, and the defining composite
unit of the Leray comparison.
(blueprint: lem-sbc-derived-section-pullback-zero).

Proof: Put R = W^* G. Compare the source with R[0] by the exact inverse-image
single comparison. Naturality of the derived unit moves that comparison through
pullback. Resolve R and f^*R by bounded-below injective resolutions and lift the
underived adjunction unit to the resolutions. The derived unit is characterized
by its composite with the right-derived unit, so the lifted morphism computes
it. The Leray comparison is characterized by its composite unit, hence its
composite with that morphism is the lift of the ordinary section pullback.
In degree zero the augmentations identify the kernels of the first differentials
with the original sheaves, because sections are left exact. These are exactly
the homologyRightDerivedFunctorObjSingleFunctorIso and rightDerivedZeroIsoSelf
comparisons in the formula. Cancel the resolution augmentations and the exact
single comparisons to obtain the stated equation. No pullback of sections is
inverted; the argument works for empty schemes and arbitrary sheaves. -/
theorem derivedSectionPullback_zero {Y X : Scheme.{v}} (W : Y.Etale)
    (f : X ⟶ W.left) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (let τ : rightDerivedGlobalSections AddCommGrpCat.{v + 1} W.left ⟶
        D(upperStar AddCommGrpCat.{v + 1} f) ⋙
          rightDerivedGlobalSections AddCommGrpCat.{v + 1} X :=
      Functor.whiskerRight
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} W.left) ≫
      Functor.whiskerLeft D(upperStar AddCommGrpCat.{v + 1} f)
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom
    let L := upperStar AddCommGrpCat.{v + 1} W.hom
    let Q := upperStar AddCommGrpCat.{v + 1} f
    let R := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
    let b := L.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app G
    let c := Q.mapDerivedCategory.map b.hom ≫
      (Q.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
    let z := R.homologyRightDerivedFunctorObjSingleFunctorIso (Q.obj (L.obj G)) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (Q.obj (L.obj G))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (τ.app
          (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map c) ≫ z.hom =
      (zeroIso W G).hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f (L.obj G)) := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
