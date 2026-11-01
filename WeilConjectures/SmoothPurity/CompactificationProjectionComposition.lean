/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SmoothPurity.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange

/-! # Projection maps on a compatible compactification tower

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B and 0F7J,
and Cohomology on Sites, Tag 0E48.
-/

@[expose] public section

set_option autoImplicit false

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor leftDerivedUpperStarTensorComparison

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

attribute [local instance] towerOpen_isOpen
attribute [local irreducible] towerOpen

section Generic
set_option backward.defeqAttrib.useBackward true

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

omit [UpperStarPreservesFlat B] in
set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor projectionMapOfCompactification
  derivedOpenImmersionLowerShriekProjectionIso rightDerivedLowerStarComp

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  openImmersionLowerShriek upperStar lowerStar

attribute [local irreducible] rightDerivedLowerStarProjectionMap
  openImmersionLowerShriekLowerStarExchange
  mapDerivedCategoryOpenImmersionLowerShriekComp mapDerivedCategoryOpenImmersionLowerShriekCongr

attribute [local irreducible] leftDerivedUpperStarComp derivedSquareUpperStarIso
  leftDerivedUpperStarCompactificationIso

omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
private noncomputable def properStrength
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (lowerStar B q).rightDerivedFunctor ⋙ (derivedTensor B Y).flip.obj N ⟶
      (derivedTensor B X).flip.obj ((upperStar B q).leftDerivedFunctor.obj N) ⋙
        (lowerStar B q).rightDerivedFunctor :=
  ((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap B q)).app N

omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
attribute [local irreducible] openStrength properStrength properTwistedStrength

omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
omit [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
end Generic

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

local instance essentiallySmall_etale_shriekTensor (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor projectionMapOfCompactification
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  openImmersionLowerShriek upperStar lowerStar

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] derivedOpenImmersionLowerShriekProjectionIso
  rightDerivedLowerStarComp rightDerivedLowerStarProjectionMap
  openImmersionLowerShriekLowerStarExchange mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekCongr leftDerivedUpperStarComp
  derivedSquareUpperStarIso leftDerivedUpperStarCompactificationIso

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationCompIso

end AlgebraicGeometry.Etale
