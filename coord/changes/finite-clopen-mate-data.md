# AlgebraicGeometry.ProEtale.cbcClopenAlphaPlus and its canonical construction data

## Reason

Separate the geometric alpha comparison (original proof steps 2--4) from the proper-mate
transport (steps 5--7). The alpha theorem must refer to the canonical constructions
without importing the theorem which uses it. Move the six existing definitions to
`Sheaf.AlgebraicGeometry.FiniteClopenMateData`, publicly reexported by the original
module. Their names, signatures, attributes, universes, instance arguments and bodies
are unchanged. No target statement or mathematical definition changes. This is a module
organization change, not a different normalization or a choice of a new object.

## Old

Defined in `Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport`:

```lean
/-- Equality transport for the canonical open extension functors.
Source: Stacks 09AF (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcOpenCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- Equality transport for inverse image, with its fixed canonical construction.
Source: Stacks 099R (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcPullCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} (h : j = k) :
    upperStar (ModuleCat.{u + 1} Λ) j ≅ upperStar (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- The identity/zero projection onto a clopen subscheme, on module sheaves.
It is the direct-image unit followed by the inverse of the canonical map
from extension by zero to direct image. Source: Stacks Tags 09AE and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenProjection (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶
      upperStar (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) s)
      (inv (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s))

/-- The canonical sheaf alpha: inverse open-unit base change, projection onto the
clopen lift, and the canonical open and inverse-image compositors.
Source: Stacks Tags 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaSheaf (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip
  inv (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip.toCommSq) ≫
  Functor.whiskerRight
    (Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
      (cbcClopenProjection Λ (ProEtale.StrictTower.squareLift k r p i h)))
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator _ _ _).inv
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft
    (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
      upperStar (ModuleCat.{u + 1} Λ) (ProEtale.StrictTower.squareLift k r p i h))
    ((proEtaleOpenExtensionComp Λ
        (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).inv ≫
      (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((upperStarComp (ModuleCat.{u + 1} Λ)
      (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (cbcPullCongr Λ (pullback.lift_snd k r h)).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)

/-- The same prescribed alpha on bounded-below derived categories. Exactness of all
four sheaf functors identifies the right-derived base-change map with termwise alpha.
Source: Stacks Tags 015F, 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaPlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  Functor.whiskerRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)).inv _ ≫
  Functor.rightDerivedFunctorPlusBaseChange (cbcClopenAlphaSheaf Λ k i r p h) ≫
  Functor.whiskerLeft _
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).hom

/-- The proper-adjunction mate of the specified clopen alpha on this site.
Source: Stacks Tags 0B65 and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (mateEquiv (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (cbcClopenAlphaPlus Λ k i r p h))).natTrans

```

## New

Defined verbatim in `Sheaf.AlgebraicGeometry.FiniteClopenMateData`:

```lean
/-- Equality transport for the canonical open extension functors.
Source: Stacks 09AF (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcOpenCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j = k) : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- Equality transport for inverse image, with its fixed canonical construction.
Source: Stacks 099R (blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcPullCongr (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} {j k : U ⟶ X} (h : j = k) :
    upperStar (ModuleCat.{u + 1} Λ) j ≅ upperStar (ModuleCat.{u + 1} Λ) k :=
  h ▸ Iso.refl _

/-- The identity/zero projection onto a clopen subscheme, on module sheaves.
It is the direct-image unit followed by the inverse of the canonical map
from extension by zero to direct image. Source: Stacks Tags 09AE and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenProjection (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶
      upperStar (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).unit ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) s)
      (inv (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s))

/-- The canonical sheaf alpha: inverse open-unit base change, projection onto the
clopen lift, and the canonical open and inverse-image compositors.
Source: Stacks Tags 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaSheaf (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip
  inv (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback p i).flip.toCommSq) ≫
  Functor.whiskerRight
    (Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
      (cbcClopenProjection Λ (ProEtale.StrictTower.squareLift k r p i h)))
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator _ _ _).inv
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft
    (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
      upperStar (ModuleCat.{u + 1} Λ) (ProEtale.StrictTower.squareLift k r p i h))
    ((proEtaleOpenExtensionComp Λ
        (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).inv ≫
      (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((upperStarComp (ModuleCat.{u + 1} Λ)
      (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (cbcPullCongr Λ (pullback.lift_snd k r h)).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)

/-- The same prescribed alpha on bounded-below derived categories. Exactness of all
four sheaf functors identifies the right-derived base-change map with termwise alpha.
Source: Stacks Tags 015F, 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenAlphaPlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  Functor.whiskerRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)).inv _ ≫
  Functor.rightDerivedFunctorPlusBaseChange (cbcClopenAlphaSheaf Λ k i r p h) ≫
  Functor.whiskerLeft _
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).hom

/-- The proper-adjunction mate of the specified clopen alpha on this site.
Source: Stacks Tags 0B65 and 0F7B
(blueprint: lem-cbc-finite-clopen-mate-site-transport). -/
def cbcClopenMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlus :=
  (mateEquiv (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r)
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) p)
    (TwoSquare.mk _ _ _ _ (cbcClopenAlphaPlus Λ k i r p h))).natTrans

```

The old module adds `public import Sheaf.AlgebraicGeometry.FiniteClopenMateData` and
continues to expose every original public import. There are no consumer adaptations.

## Users

`tools/downstream.py` was run for all six declaration names. The only direct importer
is `Sheaf.Paper.SystemCompatibleCompositorNormalization`; the declaration-name search
finds uses only in the item itself. The downstream theorem retains the same statement
and all names remain available through its original import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport | S4 | Reexports unchanged data; proves the original theorem from alpha transport. |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed (landed) | Original import and declarations remain valid; no edit. |
| Sheaf.AlgebraicGeometry.FiniteClopenMateData | S4 (new module) | Contains the six unchanged constructions. |
| Sheaf.AlgebraicGeometry.FiniteClopenAlphaSiteTransport | S4 (new module) | States the geometric/exact-localization alpha comparison. |

## Status

landed 20261024T020314-L-2580794 2026-10-24 (merge of deliver/S4/Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport)
