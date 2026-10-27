# WeilConjectures.ConstantPurityFrobenius.systems

## Reason

The profile attributes about 15 seconds to synthesis of the identity morphism's
locally-finite-type instance at the start of systems. Select the public Mathlib
open-immersion implication explicitly instead of searching for that instance.
Only this proof argument changes. The returned System type and every geometric
map and coefficient datum stay definitionally equal by proof irrelevance.

## Old

```lean
def systems :=
  letI : LocallyOfFiniteType (point D).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
  letI : QuasiCompact (point D).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated (pointMap D X₀).left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType (pointMap D X₀).left :=
    inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact (pointMap D X₀).left := inferInstanceAs (QuasiCompact X₀.hom)
  @ConstructibleExceptionalCoefficients.System l inferInstance Ω
    inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber (point D)).left
    (FrobeniusExchange.fiberMap D (pointMap D X₀)) inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (FrobeniusExchange.fiber_finiteType D (point D)).1
    (FrobeniusExchange.fiber_finiteType D (point D)).2
    (zlFiberMap_isOver D (pointMap D X₀))
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.2
```

## New

```lean
def systems :=
  letI : LocallyOfFiniteType (point D).hom :=
    locallyOfFiniteType_of_isOpenImmersion (𝟙 (Spec (.of D.k₀)))
  letI : QuasiCompact (point D).hom :=
    inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  letI : IsSeparated (pointMap D X₀).left := inferInstanceAs (IsSeparated X₀.hom)
  letI : LocallyOfFiniteType (pointMap D X₀).left :=
    inferInstanceAs (LocallyOfFiniteType X₀.hom)
  letI : QuasiCompact (pointMap D X₀).left := inferInstanceAs (QuasiCompact X₀.hom)
  @ConstructibleExceptionalCoefficients.System l inferInstance Ω
    inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber (point D)).left
    (FrobeniusExchange.fiberMap D (pointMap D X₀)) inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (FrobeniusExchange.fiber_finiteType D (point D)).1
    (FrobeniusExchange.fiber_finiteType D (point D)).2
    (zlFiberMap_isOver D (pointMap D X₀))
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.1
    (FrobeniusExchange.fiberMap_properties D (pointMap D X₀)).2.2
```

## Users

There are no current direct importers of the item module. All uses in the item
retain the same System type; the changed argument is a proposition proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | C4 | Explicit proof of the identity's finite type. |

## Status

landed 20261027T034621-L-3666357 2026-10-27 (merge of deliver/C4/Sheaf.Paper.ConstantPurityFrobeniusSquare)
