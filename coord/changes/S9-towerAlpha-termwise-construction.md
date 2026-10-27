# AlgebraicGeometry.ProEtale.StrictTower.towerAlpha

## Reason

The concrete termwise lifting definition repeatedly unfolds large module-functor
constructions during kernel comparison. A definitions-only diagnostic takes about
17 seconds checking this declaration. Package the existing four-factor termwise
lifting generically as `Functor.termwiseCompositeTransformation`, then specialize
it to the same ordinary arrow. The repaired definitions-only diagnostic takes
117 milliseconds in total kernel checking. This is a construction repair; no
proof is split into another file to evade the compile limit.

## Old

```lean
def towerAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : towerJ B i ⋙ towerPullback B p ⟶
      towerPullback B r ⋙ towerJ B k :=
  (Functor.whiskeringRightObjCompIso (moduleJ B i) (modulePullback B p)).inv ≫
    (Functor.whiskeringRight ℕᵒᵖ (Modules B S) (Modules B W)).map
      (singleAlpha B k r p i h) ≫
    (Functor.whiskeringRightObjCompIso (modulePullback B r) (moduleJ B k)).hom
```

## New

```lean
def towerAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : towerJ B i ⋙ towerPullback B p ⟶
      towerPullback B r ⋙ towerJ B k :=
  Functor.termwiseCompositeTransformation ℕᵒᵖ (Modules B S) (Modules B T)
    (Modules B V) (Modules B W) (moduleJ B i) (modulePullback B p)
    (modulePullback B r) (moduleJ B k) (singleAlpha B k r p i h)
```

Both composition isomorphisms are definitionally `Iso.refl`. Thus swapping the
hom/inverse orientation in the generic constructor does not change any map.
At a diagram M and index n, both definitions give the component
`(singleAlpha B k r p i h).app (M.obj n)`. All public types are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows | S9 | Same type and same termwise components. |

## Status

landed 20261024T191117-L-247651 2026-10-24 (merge of deliver/S9/Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows)
Delivery runs the final clean compile and preflight. The sole direct user is this item;
no consumer adaptation is required.
