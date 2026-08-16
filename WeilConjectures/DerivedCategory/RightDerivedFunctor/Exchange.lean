/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The exchange transformation of right derived functors along exact functors

Consider a square of additive functors between abelian categories

```
C --F--> D
|        |
U        V
v        v
C' -F'-> D'
```

together with a natural transformation `τ : F ⋙ V ⟶ U ⋙ F'`, where the vertical
functors `U` and `V` are *exact* and the horizontal functors `F` and `F'` are right
derivable on the bounded below derived categories (their sources have enough
injectives). This file constructs the canonical *exchange transformation*

`RF ⋙ V ⟶ U ⋙ RF'`

on the bounded below derived categories, where the exact functors are derived
levelwise by `Functor.mapDerivedCategoryPlus` (no resolutions are needed) and the
horizontal functors by `Functor.rightDerivedFunctorPlus` (via injective resolutions).

The construction is the one of the Grothendieck composition theorem for right derived
functors: since `V` is exact, the composite `F.rightDerivedFunctorPlus ⋙
V.mapDerivedCategoryPlus` is itself a right derived functor of `F ⋙ V` — this is the
case of the composition theorem requiring no acyclicity hypothesis, because *every*
object is acyclic for the exact outer functor — and the exchange transformation is
obtained from its universal property (as a left Kan extension along the localization
`DerivedCategory.Plus.Qh`) applied to `U.mapDerivedCategoryPlus ⋙
F'.rightDerivedFunctorPlus` equipped with its composite unit.

The exchange transformation is *not* an isomorphism in general: by the composition
theorem it is one as soon as `U` sends injective objects to `F'`-acyclic objects.
This acyclicity input is specific to the applications and is not formalized here.

## Main definitions

- `CategoryTheory.Functor.mapHomotopyCategoryPlusCompatibility` and
  `CategoryTheory.NatTrans.mapHomotopyCategoryPlus`: compatibility with the inclusions
  and functoriality in natural transformations of `Functor.mapHomotopyCategoryPlus`.
- `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh`: the functor
  `V.mapDerivedCategoryPlus` induced on the bounded below derived categories by an
  exact functor `V` is induced by `V.mapHomotopyCategoryPlus` under the localizations
  `DerivedCategory.Plus.Qh`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit`: the
  composite unit exhibiting `RF ⋙ V` as a right derived functor of `F ⋙ V`, with the
  corresponding `IsRightDerivedFunctor` instance.
- `CategoryTheory.Functor.mapDerivedCategoryPlusCompRightDerivedFunctorPlusUnit`: the
  composite unit of the candidate `U ⋙ RF'` for `U ⋙ F'`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusExchange`: the exchange
  transformation `RF ⋙ V ⟶ U ⋙ RF'` associated with `τ : F ⋙ V ⟶ U ⋙ F'`.

-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

section MapHomotopyCategoryPlus

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- The functor `F.mapHomotopyCategoryPlus` induced on the bounded below homotopy
categories by an additive functor `F` is compatible with the inclusions into the
unbounded homotopy categories. -/
def Functor.mapHomotopyCategoryPlusCompatibility (F : C ⥤ D) [F.Additive] :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ≅
      HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Iso.refl _

/-- Functoriality of `Functor.mapHomotopyCategoryPlus` in natural transformations:
a natural transformation `F ⟶ G` of additive functors induces a natural transformation
of the functors induced on the bounded below homotopy categories. It is obtained from
`NatTrans.mapHomotopyCategory` by cancelling the fully faithful inclusions
`HomotopyCategory.Plus.ι`. -/
def NatTrans.mapHomotopyCategoryPlus {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)))

end MapHomotopyCategoryPlus

namespace Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factorsh

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- The functor `V.mapDerivedCategoryPlus` induced on the bounded below derived
categories by an exact functor `V` is induced by `V.mapHomotopyCategoryPlus` under the
localization functors `DerivedCategory.Plus.Qh`: the bounded below analogue of
`Functor.mapDerivedCategoryFactorsh`, obtained from it by cancelling the fully
faithful inclusions `DerivedCategory.Plus.ι`. -/
noncomputable def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ V.mapDerivedCategoryPlus ≅
      V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft DerivedCategory.Plus.Qh V.mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh C) V.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (HomotopyCategory.Plus.ι C) V.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight V.mapHomotopyCategoryPlusCompatibility.symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft V.mapHomotopyCategoryPlus (DerivedCategory.Plus.QhCompιIsoιCompQh D).symm ≪≫
      (Functor.associator _ _ _).symm)

end Factorsh

section CompUnits

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory C']
  [HasDerivedCategory D] [HasDerivedCategory D']

section Left

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
  (V : D ⥤ D') [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- The composite unit exhibiting `F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus`
as a right derived functor of `F ⋙ V` on the bounded below derived categories, for `F`
additive and `V` exact: it is assembled from the unit of `RF`, the factorization
`Functor.mapDerivedCategoryPlusFactorsh` of the levelwise functor of `V`, and the
composition isomorphism of `mapHomotopyCategoryPlus`. -/
noncomputable def rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit :
    (F ⋙ V).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ V))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus V.mapDerivedCategoryPlusFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit V.mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom

/-- The case of the Grothendieck composition theorem requiring no acyclicity input:
for an *exact* outer functor `V`, the composite `RF ⋙ V` of the right derived functor
of `F` with the levelwise functor of `V`, equipped with the composite unit, is a right
derived functor of `F ⋙ V` on the bounded below derived categories. By the injective
right derivability structure it suffices that the composite unit is an isomorphism on
bounded below complexes of injectives, which holds since the unit of `RF` is and the
remaining ingredients of the composite unit are isomorphisms everywhere. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp_mapDerivedCategoryPlus :
    (F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit F V)
      (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ V).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso
      _ (fun X₁ ↦ by
        have : IsIso (F.rightDerivedFunctorPlusUnit.app
            ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁)) := inferInstance
        dsimp [rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit]
        simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app]
        infer_instance)

end Left

section Right

variable (U : C ⥤ C') [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (F' : C' ⥤ D') [F'.Additive] [EnoughInjectives C']

/-- The composite unit exhibiting `U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus`
as a *candidate* right derived functor of `U ⋙ F'` on the bounded below derived
categories, for `U` exact and `F'` additive. In contrast to
`Functor.rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit`, this candidate is an
actual right derived functor only under an acyclicity hypothesis (`U` should send
injective objects to `F'`-acyclic objects); no such hypothesis enters the definition
of the unit. -/
noncomputable def mapDerivedCategoryPlusCompRightDerivedFunctorPlusUnit :
    (U ⋙ F').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (U ⋙ F'))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft U.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight U.mapDerivedCategoryPlusFactorsh.inv F'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

end Right

section Exchange

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
  (F' : C' ⥤ D') [F'.Additive] [EnoughInjectives C']
  (U : C ⥤ C') [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (V : D ⥤ D') [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]

/-- The *exchange transformation* `RF ⋙ V ⟶ U ⋙ RF'` on the bounded below derived
categories associated with a square `τ : F ⋙ V ⟶ U ⋙ F'` of additive functors between
abelian categories with exact vertical functors `U`, `V`: since `RF ⋙ V` is a right
derived functor of `F ⋙ V` (the exact-outer-functor case of the composition theorem,
`Functor.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_mapDerivedCategoryPlus`),
its universal property applied to the candidate `U ⋙ RF'` with its composite unit
yields the canonical comparison.

It is an isomorphism whenever `τ` is an isomorphism and `U` sends injective objects to
`F'`-acyclic objects; this acyclicity input is left to the applications. -/
noncomputable def rightDerivedFunctorPlusExchange (τ : F ⋙ V ⟶ U ⋙ F') :
    F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ⟶
      U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatTrans _ _
    (rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit F V)
    (mapDerivedCategoryPlusCompRightDerivedFunctorPlusUnit U F')
    (HomotopyCategory.Plus.quasiIso C)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) DerivedCategory.Plus.Qh)

/-- The defining property of the exchange transformation: it is compatible with the
composite units of `RF ⋙ V` and `U ⋙ RF'` under the localization
`DerivedCategory.Plus.Qh`. -/
@[reassoc]
lemma rightDerivedFunctorPlusExchange_fac (τ : F ⋙ V ⟶ U ⋙ F') :
    rightDerivedFunctorPlusCompMapDerivedCategoryPlusUnit F V ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusExchange F F' U V τ) =
    Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) DerivedCategory.Plus.Qh ≫
      mapDerivedCategoryPlusCompRightDerivedFunctorPlusUnit U F' :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

end Exchange

end CompUnits

end Functor

end CategoryTheory
