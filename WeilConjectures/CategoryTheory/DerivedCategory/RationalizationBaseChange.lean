/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Completed
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement

/-!
# Base change squares and rationalization

Let `𝔇` be a base change square (`CategoryTheory.BaseChangeSquare`) of `R`-linear triangulated
categories and `R`-linear triangulated functors

```
  𝒳  --g'^*-->  𝒳'
  ↑ f^*          ↑ f'^*
  𝒴  --g^*--->  𝒴'
```

with adjunctions `f^* ⊣ f_*`, `f'^* ⊣ f'_*` and Cartesian identification
`g^* ⋙ f'^* ≅ f^* ⋙ g'^*`, and let `M` be a submonoid of `R`. All the data transport to the
rationalizations `Rationalization M -` (blueprint `prop-weil-pbc-rational-transport`): this
gives the *rationalized base change square* `𝔇.rationalization M`, whose functors are the
`Rationalization.map M` of those of `𝔇`. The localization functors `Q` form a reduction of base
change squares `𝔇 ⟶ 𝔇.rationalization M` whose projection maps are invertible, so the exchange
rectangle identifies the exchange map of the rationalized square at `Q K` with the image under
`Q` of the exchange map of `𝔇` at `K`. In particular, if the integral exchange map is an
isomorphism, so is the rationalized one (blueprint `thm-weil-pbc-finite-extension`: for
`R = 𝒪_E`, `M` the powers of a uniformizer, and `𝔇` the proper base change square of the integral
constructible complete categories `D^b_c(-, 𝒪_E)`, whose exchange map is an isomorphism by
`cor-weil-pbc-constructible-complete`).

## Main definitions

- `CategoryTheory.BaseChangeSquare.rationalization`: the rationalized base change square.
- `CategoryTheory.BaseChangeSquare.rationalizationReduction`: the reduction of `𝔇` into its
  rationalization given by the localization functors.

## Main statements

- `CategoryTheory.BaseChangeSquare.isIso_rationalization_exchange_app_iff`: the rationalized
  exchange map is invertible at `Q K` iff the image of the integral exchange map at `K` is.
- `CategoryTheory.BaseChangeSquare.isIso_rationalization_exchange`: if the integral exchange map
  is an isomorphism, so is the rationalized one.
-/

@[expose] public section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory

namespace Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]
  {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R]

/-- The mate of the factorization `Q ⋙ map F ≅ F ⋙ Q` with respect to an adjunction `F ⊣ G` and
its rationalization is the factorization of `G`: the "projection map"
`G ⋙ Q ⟶ Q ⋙ map G` is `(mapFac M G).inv`. -/
lemma mateEquiv_mapFac_hom (adj : F ⊣ G) :
    mateEquiv adj (mapAdjunction M adj) (mapFac M F).hom = (mapFac M G).inv := by
  ext Y
  have h := (mapFac M G).inv.naturality (adj.counit.app Y)
  dsimp at h
  rw [mateEquiv_apply]
  dsimp only [TwoSquare.natTrans]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.comp_id, mapAdjunction_unit_app, Category.assoc]
  erw [Functor.map_id, Category.id_comp]
  rw [← h,
    ← Functor.map_comp_assoc, adj.right_triangle_components, Functor.map_id, Category.id_comp]

end Rationalization

namespace BaseChangeSquare

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] [Preadditive 𝒳] [Linear R 𝒳] [HasZeroObject 𝒳]
  [HasShift 𝒳 ℤ] [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒳 n).Linear R]
  [Pretriangulated 𝒳] [IsTriangulated 𝒳]
  {𝒴 : Type u₂} [Category.{v₂} 𝒴] [Preadditive 𝒴] [Linear R 𝒴] [HasZeroObject 𝒴]
  [HasShift 𝒴 ℤ] [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒴 n).Linear R]
  [Pretriangulated 𝒴] [IsTriangulated 𝒴]
  {𝒳' : Type u₃} [Category.{v₃} 𝒳'] [Preadditive 𝒳'] [Linear R 𝒳'] [HasZeroObject 𝒳']
  [HasShift 𝒳' ℤ] [∀ n : ℤ, (shiftFunctor 𝒳' n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒳' n).Linear R] [Pretriangulated 𝒳'] [IsTriangulated 𝒳']
  {𝒴' : Type u₄} [Category.{v₄} 𝒴'] [Preadditive 𝒴'] [Linear R 𝒴'] [HasZeroObject 𝒴']
  [HasShift 𝒴' ℤ] [∀ n : ℤ, (shiftFunctor 𝒴' n).Additive]
  [∀ n : ℤ, (shiftFunctor 𝒴' n).Linear R] [Pretriangulated 𝒴'] [IsTriangulated 𝒴']
  (𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴')
  [𝔇.upperF.CommShift ℤ] [𝔇.upperF.IsTriangulated] [𝔇.upperF.Linear R]
  [𝔇.lowerF.CommShift ℤ] [𝔇.lowerF.IsTriangulated] [𝔇.lowerF.Linear R]
  [𝔇.upperF'.CommShift ℤ] [𝔇.upperF'.IsTriangulated] [𝔇.upperF'.Linear R]
  [𝔇.lowerF'.CommShift ℤ] [𝔇.lowerF'.IsTriangulated] [𝔇.lowerF'.Linear R]
  [𝔇.upperG.CommShift ℤ] [𝔇.upperG.IsTriangulated] [𝔇.upperG.Linear R]
  [𝔇.upperG'.CommShift ℤ] [𝔇.upperG'.IsTriangulated] [𝔇.upperG'.Linear R]

open Rationalization

/-- The Cartesian identification of the rationalized square: the unique isomorphism
`map g^* ⋙ map f'^* ≅ map f^* ⋙ map g'^*` lifting the Cartesian identification of `𝔇`. -/
noncomputable def rationalizationIso :
    map M 𝔇.upperG ⋙ map M 𝔇.upperF' ≅ map M 𝔇.upperF ⋙ map M 𝔇.upperG' :=
  Localization.liftNatIso (Q M 𝒴) (W M 𝒴) ((𝔇.upperG ⋙ 𝔇.upperF') ⋙ Q M 𝒳')
    ((𝔇.upperF ⋙ 𝔇.upperG') ⋙ Q M 𝒳') _ _ (Functor.isoWhiskerRight 𝔇.iso _)

/-- Blueprint `prop-weil-pbc-rational-transport` (for base change squares): the rationalization
of a base change square of `R`-linear triangulated categories, whose functors and adjunctions
are induced on the rationalizations by those of `𝔇`. -/
@[simps]
noncomputable def rationalization :
    BaseChangeSquare (Rationalization M 𝒳) (Rationalization M 𝒴) (Rationalization M 𝒳')
      (Rationalization M 𝒴') where
  upperF := map M 𝔇.upperF
  lowerF := map M 𝔇.lowerF
  adjF := mapAdjunction M 𝔇.adjF
  upperF' := map M 𝔇.upperF'
  lowerF' := map M 𝔇.lowerF'
  adjF' := mapAdjunction M 𝔇.adjF'
  upperG := map M 𝔇.upperG
  upperG' := map M 𝔇.upperG'
  iso := 𝔇.rationalizationIso M

lemma rationalizationIso_hom_app (Y : 𝒴) :
    (𝔇.rationalizationIso M).hom.app ((Q M 𝒴).obj Y) =
      (map M 𝔇.upperF').map ((mapFac M 𝔇.upperG).hom.app Y) ≫
        (mapFac M 𝔇.upperF').hom.app (𝔇.upperG.obj Y) ≫ (Q M 𝒳').map (𝔇.iso.hom.app Y) ≫
        (mapFac M 𝔇.upperG').inv.app (𝔇.upperF.obj Y) ≫
        (map M 𝔇.upperG').map ((mapFac M 𝔇.upperF).inv.app Y) := by
  simp [rationalizationIso, Localization.liftNatIso, Localization.liftNatTrans_app,
    liftingMapComp]

/-- The localization functors form a reduction of a base change square into its
rationalization, the comparisons being the factorizations `Q ⋙ map F ≅ F ⋙ Q`. -/
noncomputable def rationalizationReduction : Reduction 𝔇 (𝔇.rationalization M) where
  redX := Q M 𝒳
  redY := Q M 𝒴
  redX' := Q M 𝒳'
  redY' := Q M 𝒴'
  γF := (mapFac M 𝔇.upperF).hom
  γF' := (mapFac M 𝔇.upperF').hom
  δG := mapFac M 𝔇.upperG
  δG' := mapFac M 𝔇.upperG'
  cube := by
    ext Y
    simp [rationalizationIso_hom_app]

lemma rationalizationReduction_projF :
    (𝔇.rationalizationReduction M).projF = (mapFac M 𝔇.lowerF).inv :=
  mateEquiv_mapFac_hom M 𝔇.adjF

lemma rationalizationReduction_projF' :
    (𝔇.rationalizationReduction M).projF' = (mapFac M 𝔇.lowerF').inv :=
  mateEquiv_mapFac_hom M 𝔇.adjF'

instance (K : 𝒳) : IsIso ((𝔇.rationalizationReduction M).projF.natTrans.app K) := by
  rw [rationalizationReduction_projF]
  infer_instance

instance (K : 𝒳') : IsIso ((𝔇.rationalizationReduction M).projF'.natTrans.app K) := by
  rw [rationalizationReduction_projF']
  infer_instance

/-- The exchange map of the rationalized square at the rationalization `Q K` of an object `K`
is invertible if and only if the rationalization of the exchange map of `𝔇` at `K` is. -/
lemma isIso_rationalization_exchange_app_iff (K : 𝒳) :
    IsIso ((𝔇.rationalization M).exchange.natTrans.app ((Q M 𝒳).obj K)) ↔
      IsIso ((Q M 𝒴').map (𝔇.exchange.natTrans.app K)) :=
  ((𝔇.rationalizationReduction M).isIso_redY'_map_exchange_app_iff K).symm

/-- Blueprint `thm-weil-pbc-finite-extension` (rational transport of the exchange isomorphism):
if the exchange map `g^* f_* ⟶ f'_* g'^*` of a base change square of `R`-linear triangulated
categories is an isomorphism, so is the exchange map of its rationalization. -/
theorem isIso_rationalization_exchange [IsIso 𝔇.exchange.natTrans] :
    IsIso (𝔇.rationalization M).exchange.natTrans :=
  isIso_of_isIso_app_Q _ fun K ↦ (𝔇.isIso_rationalization_exchange_app_iff M K).2 inferInstance

end BaseChangeSquare

end CategoryTheory
