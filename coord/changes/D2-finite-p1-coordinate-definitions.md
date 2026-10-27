# finiteUnitCoordinate, finiteOverRealization, finiteOverUnitCoordinate

## Reason

Move these three existing definitions to
`Sheaf.Paper.FiniteP1CoefficientCoordinateDefinitions`, publicly reexported by the
original item. The normalized coordinate-existence and adjunction helpers can then
be imported by the item without an import cycle. Their names, signatures, bodies,
visibility, and effective public dependencies remain identical. No target changes
meaning, so no target statement review is reopened by this relocation.

## Old

In `Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates`:

```lean
def finiteUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (SpTowerShriek.Ev l E T n).obj (unit T (Arings l E T)) ≅
      (Scheme.sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory.obj
        (geoP1Unit (FiniteRing l E n) T) :=
  (SpTowerP1.nuSingle l E n T _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c.unit ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).symm

/-- Realize a fixed-scalar object on P¹ on an isomorphic scheme X.
Source: diagonal-tower trace (1), transport over the base
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates). -/
abbrev finiteOverRealization (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S) :=
  geoP1Pullback (FiniteRing l E n) e.hom ⋙
    (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor.mapDerivedCategory

/-- The normalized source comparison, including pullback along e.
Source: diagonal-tower trace (1), coefficient units
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates). -/
def finiteOverUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    (SpTowerShriek.Ev l E X n).obj (unit X (Arings l E X)) ≅
      (finiteOverRealization l E n e).obj (geoP1Unit (FiniteRing l E n) (ProjectiveLine S)) :=
  finiteUnitCoordinate l E n X c ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1UnitPullback (FiniteRing l E n) e.hom).symm
```

## New

In `Sheaf.Paper.FiniteP1CoefficientCoordinateDefinitions`, with the original
module publicly importing this module:

```lean
def finiteUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT) :
    (SpTowerShriek.Ev l E T n).obj (unit T (Arings l E T)) ≅
      (Scheme.sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).functor.mapDerivedCategory.obj
        (geoP1Unit (FiniteRing l E n) T) :=
  (SpTowerP1.nuSingle l E n T _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c.unit ≪≫
    (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _).symm).symm

/-- Realize a fixed-scalar object on P¹ on an isomorphic scheme X.
Source: diagonal-tower trace (1), transport over the base
(blueprint: def-sfb-finite-p1-coefficient-coordinate-definitions). -/
abbrev finiteOverRealization (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S) :=
  geoP1Pullback (FiniteRing l E n) e.hom ⋙
    (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor.mapDerivedCategory

/-- The normalized source comparison, including pullback along e.
Source: diagonal-tower trace (1), coefficient units
(blueprint: def-sfb-finite-p1-coefficient-coordinate-definitions). -/
def finiteOverUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    (SpTowerShriek.Ev l E X n).obj (unit X (Arings l E X)) ≅
      (finiteOverRealization l E n e).obj (geoP1Unit (FiniteRing l E n) (ProjectiveLine S)) :=
  finiteUnitCoordinate l E n X c ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1UnitPullback (FiniteRing l E n) e.hom).symm
```

## Users

The `downstream.py --uses` searches for all three names give the following union.
Holder records were read from the current coordination state on 2026-10-28.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates | D2 | Publicly reexports the same definitions; proof uses them unchanged. |
| Sheaf.Paper.DiagonalTraceFiniteChernComparison | unclaimed | Same names, types and reduction behavior; no adaptation. |
| Sheaf.Paper.FiniteP1KummerBoundaryTransport | D3 | Same names, types and reduction behavior; no adaptation. |
| Sheaf.Paper.FiniteP1KummerChernRealization | unclaimed | Same names, types and reduction behavior; no adaptation. |
| Sheaf.Paper.FiniteP1KummerComparisonIso | unclaimed | Same names, types and reduction behavior; no adaptation. |

The three Kummer modules are every direct importer of the original item.
The finite Chern comparison is also checked because it mentions the relocated names.
No existing module outside the item is modified.

## Status

landed 20261027T205858-L-1628476 2026-10-27 (merge of deliver/D2/Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates)
