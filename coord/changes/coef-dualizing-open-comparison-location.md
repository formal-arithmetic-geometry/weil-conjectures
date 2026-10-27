# Open comparison definitions: module location

## Reason

Move the four existing real comparison definitions unchanged beside the bounded-below
substep theorem. Repeating their constructions in a separate theorem caused expensive
kernel conversions. The item publicly imports the new module, preserving the same
names, signatures, values and availability to importers. No source-library file changes.

## Old

Defined in `Sheaf.Paper.CoefficientDualizingOpenAdjoint`:

```lean
def coefDualizingOpenNormalization
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [HasCompactification j] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} R) j ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  (rightDerivedLowerShriekIso R (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory
      (rightDerivedLowerStarIdIso R Y) ≪≫ Functor.rightUnitor _


def coefDualizingOpenLeftIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} R) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} R) (j ≫ f) :=
  Functor.isoWhiskerRight (coefDualizingOpenNormalization R j).symm _ ≪≫
    unboundedEtaleLowerShriekCompIso R j f


def coefDualizingOpenLeftPlusIso
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) f ≅
      rightDerivedLowerShriekPlus (ModuleCat.{u + 1} R) (j ≫ f) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationPlusIso R
          (HasCompactification.compactification j) (Compactification.ofIsOpenImmersion j) ≪≫
        Functor.isoWhiskerLeft
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus
          (lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) Y) ≪≫
        Functor.rightUnitor _).symm _ ≪≫
    rightDerivedLowerShriekPlusCompIso R j f


def CoefDualizingOpenPlusStatement
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y S : Scheme.{u}} (j : U ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiCompact (j ≫ f)]
    [HasCompactification j] [HasCompactification f] [HasCompactification (j ≫ f)] : Prop :=
  ∀ K : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)),
    _root_.DerivedCategory.Plus.ι.map
        ((coefDualizingOpenLeftPlusIso R j f).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) (j ≫ f)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} R) f).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus.obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} R) f).map
        ((Functor.mapDerivedCategoryPlusCompatibility
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) j)).hom.app K) ≫
      (coefDualizingOpenLeftIso R j f).hom.app (_root_.DerivedCategory.Plus.ι.obj K)

```

## New

The exact same definitions, signatures, visibility and bodies are defined in
`Sheaf.Paper.CoefficientDualizingOpenCompositorPlus`. The original module publicly
imports it; all other original declarations remain in the original module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientDualizingOpenAdjoint | M3 | Publicly imports the moved definitions; proofs completed from the bounded-below substep. |

`tools/downstream.py` reports no downstream modules. Symbol-use searches for all four
names are recorded in the work session; direct users are covered by the public import.

## Status

landed 20261025T163853-L-878364 2026-10-25 (merge of deliver/M3/Sheaf.Paper.CoefficientDualizingOpenAdjoint)
