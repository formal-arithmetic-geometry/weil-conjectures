/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Degree-zero restriction and coefficient transport

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-derived-restriction-zero-transport).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The restriction triangle and a coefficient morphism respect the zero comparison.
Source: Stacks Project, Tag 0D6F, restriction, and functoriality of localization.
(blueprint: lem-sbc-derived-restriction-zero-transport).

Proof: Expand the derived restriction isomorphism into its three factors.
The localization factorization of mapDerivedCategoryCompIso identifies each
composition factor on a single complex with its underived composition factor.
The factorization of mapDerivedCategoryNatIso identifies the middle factor with
the single of the upperStarComp comparison. The singleFunctorιIso and exact
single comparisons cancel between adjacent factors. After these cancellations
the resulting map of single complexes is the single of
rawAffineRestrictedCoefficient. Apply derived sections and zeroth homology.
Naturality of the right-derived single homology comparison, followed by
naturality of rightDerivedZeroIsoSelf, gives the section map of that coefficient
morphism. The remaining outer single comparisons are exactly those displayed
in zeroIso. This uses no invertibility of the coefficient map and also applies
to the empty scheme. -/
theorem derivedRestriction_zero_transport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ψ : (upperStar AddCommGrpCat.{v + 1} a).obj G ⟶ G') (U : S.Etale) :
    (let e : D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)) ≅
      D(upperStar AddCommGrpCat.{v + 1} a) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')) := by
      let q := rawAffineRestrictedMap a h h' w U
      let r := Limits.pullback.snd U.hom h
      let r' := Limits.pullback.snd U.hom h'
      have hw : r' ≫ a = q ≫ r := by simp [q, r, r', rawAffineRestrictedMap]
      exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso ((upperStarComp AddCommGrpCat.{v + 1} q r).symm ≪≫
          upperStarComp AddCommGrpCat.{v + 1} r' a (q ≫ r) hw.symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
    let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
    let W' := (MorphismProperty.Over.pullback @Etale ⊤ h').obj U
    let L := upperStar AddCommGrpCat.{v + 1} W.hom
    let Q := upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
    let R := Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}
    let b := L.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app G
    let c := Q.mapDerivedCategory.map b.hom ≫
      (Q.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
    let z := R.homologyRightDerivedFunctorObjSingleFunctorIso (Q.obj (L.obj G)) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (Q.obj (L.obj G))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map (e.hom.app
          (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
      (sectionsFunctor W' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map ψ) ≫ (zeroIso W' G').hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map c) ≫ z.hom ≫
          R.map (rawAffineRestrictedCoefficient a h h' w G G' ψ U)) := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
