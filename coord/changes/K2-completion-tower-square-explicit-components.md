# CategoryTheory.AdicSites.towerModuleSquare

## Reason

Kernel conversion of whiskering a composite inverse-image functor repeatedly unfolds
its concrete scalar-extension presentation. Write the identical pointwise natural
isomorphism explicitly so each naturality proof uses the existing module square.

## Old

```lean
def towerModuleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerModulePull A ⋙ k.towerModulePull A ≅
      f.towerModulePull A ⋙ h.towerModulePull A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleSquare sq A)
```

## New

```lean
def towerModuleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerModulePull A ⋙ k.towerModulePull A ≅
      f.towerModulePull A ⋙ h.towerModulePull A :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun n ↦ (moduleSquare sq A).app (M.obj n))
      (fun i ↦ (moduleSquare sq A).hom.naturality (M.map i)))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (moduleSquare sq A).hom.naturality (a.app n))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletionMateComparison | K2 | Same pointwise square and naturality; no signature change. |

The qualified-name consumer scan lists only this module (two occurrences). The
remaining import consumers use the unchanged public API. Components of the old
and new definitions are the same `moduleSquare` components.

## Status

landed 20261025T123221-L-1844305 2026-10-25 (merge of deliver/K2/Sheaf.Paper.CompletionMateComparison)
