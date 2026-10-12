/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Rectangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPasting

/-!
# Base change squares of derived categories and of towers

Let `𝔄` be a base change square (`CategoryTheory.BaseChangeSquare`) of abelian categories whose
pullbacks `f^*`, `f'^*`, `g^*`, `g'^*` are exact, as for sheaves on a cartesian square of
schemes (`def-weil-pbc-cartesian-square`). We define

* `CategoryTheory.BaseChangeSquare.mapDerived 𝔄`: the base change square of the unbounded
  derived categories, with pullbacks `D(f^*)` induced levelwise, direct images the total right
  derived functors `Rf_*`, and adjunctions `D(f^*) ⊣ Rf_*`
  (`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`);
* `CategoryTheory.BaseChangeSquare.whiskeringRight J 𝔄`: the square of the categories of
  diagrams `J ⥤ -` formed by the levelwise operations. For `J = ℕᵒᵖ` this is the square of
  towers; its derived square `(𝔄.whiskeringRight ℕᵒᵖ).mapDerived` is the square of the derived
  categories of towers `D(Tow(X))`, … with the levelwise operations `Lg^*_Tow`, `Rf_*^Tow` of
  the completed base change construction (`def-weil-pbc-completed-base-change-map`).
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory

namespace BaseChangeSquare

section MapDerived

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄] [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  (𝔄 : BaseChangeSquare C₁ C₂ C₃ C₄)
  [𝔄.upperF.Additive] [PreservesFiniteLimits 𝔄.upperF] [PreservesFiniteColimits 𝔄.upperF]
  [𝔄.upperF'.Additive] [PreservesFiniteLimits 𝔄.upperF'] [PreservesFiniteColimits 𝔄.upperF']
  [𝔄.upperG.Additive] [PreservesFiniteLimits 𝔄.upperG] [PreservesFiniteColimits 𝔄.upperG]
  [𝔄.upperG'.Additive] [PreservesFiniteLimits 𝔄.upperG'] [PreservesFiniteColimits 𝔄.upperG']
  [𝔄.lowerF.Additive] [𝔄.lowerF'.Additive]

/-- The base change square of unbounded derived categories induced by a base change square `𝔄`
of abelian categories with exact pullbacks: the pullbacks are the functors `D(f^*)` induced
levelwise, the direct images are the total right derived functors `Rf_*`, with the adjunctions
`D(f^*) ⊣ Rf_*`, and the Cartesian identification is induced by that of `𝔄`. -/
@[simps]
noncomputable def mapDerived :
    BaseChangeSquare (DerivedCategory C₁) (DerivedCategory C₂) (DerivedCategory C₃)
      (DerivedCategory C₄) where
  upperF := 𝔄.upperF.mapDerivedCategory
  lowerF := 𝔄.lowerF.rightDerivedFunctor
  adjF := 𝔄.adjF.mapDerivedCategoryRightDerivedAdjunction
  upperF' := 𝔄.upperF'.mapDerivedCategory
  lowerF' := 𝔄.lowerF'.rightDerivedFunctor
  adjF' := 𝔄.adjF'.mapDerivedCategoryRightDerivedAdjunction
  upperG := 𝔄.upperG.mapDerivedCategory
  upperG' := 𝔄.upperG'.mapDerivedCategory
  iso := Functor.mapDerivedCategorySquareIso 𝔄.iso

end MapDerived

section WhiskeringRight

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  (J : Type*) [Category* J]

/-- The base change square of diagrams `J ⥤ -` formed by the levelwise operations of a base
change square `𝔄`: the pullbacks and direct images are composition with those of `𝔄`, with the
adjunctions `Adjunction.whiskerRight`. For `J = ℕᵒᵖ` this is the square of towers
(`def-weil-pbc-adic-coefficient-datum`). -/
def whiskeringRight (𝔄 : BaseChangeSquare C₁ C₂ C₃ C₄) :
    BaseChangeSquare (J ⥤ C₁) (J ⥤ C₂) (J ⥤ C₃) (J ⥤ C₄) where
  upperF := (Functor.whiskeringRight J _ _).obj 𝔄.upperF
  lowerF := (Functor.whiskeringRight J _ _).obj 𝔄.lowerF
  adjF := 𝔄.adjF.whiskerRight J
  upperF' := (Functor.whiskeringRight J _ _).obj 𝔄.upperF'
  lowerF' := (Functor.whiskeringRight J _ _).obj 𝔄.lowerF'
  adjF' := 𝔄.adjF'.whiskerRight J
  upperG := (Functor.whiskeringRight J _ _).obj 𝔄.upperG
  upperG' := (Functor.whiskeringRight J _ _).obj 𝔄.upperG'
  iso := NatIso.ofComponents (fun M ↦ Functor.isoWhiskerLeft M 𝔄.iso) (by
    intro M N φ
    ext j
    exact (𝔄.iso.hom.naturality (φ.app j)).symm)

end WhiskeringRight

end BaseChangeSquare

end CategoryTheory
