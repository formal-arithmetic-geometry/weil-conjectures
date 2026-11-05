/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientPullbackCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityOpenExchangeCoordinates

/-! # The specified open exchange in total-derived coordinates -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {j : X ⟶ Y} {j' : X' ⟶ Y'}
  {πX : X' ⟶ X} {πY : Y' ⟶ Y}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The levelwise open exchange is the left mate for arbitrary transverse pullback. -/
lemma purityOpenDerivedExchange_inv (sq : IsPullback πX j' j πY) :
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq.flip).inv =
      Adjunction.exchangeLeft
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j')
        (Functor.mapDerivedCategorySquareIso
          (upperStarSquareComparison Λ sq.toCommSq.flip)) := by
  have he := purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv Λ sq.flip
  have : IsIso (Adjunction.exchangeLeft
      (openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openImmersionLowerShriekUpperStarAdjunction Λ j')
      (upperStarSquareComparison Λ sq.toCommSq.flip)) := by
    rw [← he]
    infer_instance
  have he' : asIso (Adjunction.exchangeLeft
      (openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openImmersionLowerShriekUpperStarAdjunction Λ j')
      (upperStarSquareComparison Λ sq.toCommSq.flip)) =
      (openImmersionLowerShriekUpperStarBaseChangeIso Λ sq.flip).symm := by
    apply Iso.ext
    exact he.symm
  rw [derivedOpenImmersionLowerShriekUpperStarAdjunction,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Adjunction.exchangeLeft_mapDerivedCategoryAdjunction, he',
    Functor.mapDerivedCategorySquareIso_symm]
  rfl

/-- The canonical left exchange is the specified derived extension-by-zero comparison,
with the transverse pullbacks changed from levelwise to total-derived coordinates. -/
lemma purityOpenAmbientExchange_eq (sq : IsPullback πX j' j πY) :
    Adjunction.exchangeLeft
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm)
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j').symm)
      (pullbackSquareComparison Λ sq.toCommSq.flip) =
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ πX).hom _ ≫
      (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq.flip).inv ≫
      Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory Λ πY).inv := by
  have he := Adjunction.purity_exchangeLeft_coordinates
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j')
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j').symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ πX)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ πY)
    (pullbackSquareComparison Λ sq.toCommSq.flip)
    (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq.toCommSq.flip))
    (purityAmbientPullbackSquareComparison_coordinates Λ sq.toCommSq.flip)
  rw [← purityOpenDerivedExchange_inv Λ sq] at he
  exact he

end AlgebraicGeometry.ProEtale.CondensedRing
