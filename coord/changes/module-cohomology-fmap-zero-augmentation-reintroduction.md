# AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_zero_augmentation

## Reason

The assigned module and its node existed when this worker started, but the base refreshed
by deliver3.py no longer contains either. The first dry run consequently classified the
item as a new interface. Restore the exact assigned theorem with a complete proof, along
with its node. No existing theorem, definition, visibility, or target statement changes.
This follows the existing etale-section-colimit-local-zero-reintroduction change record.

## Old

Absent on the refreshed base. At worker start the following signature existed with proof
`by sorry`:

```lean
theorem ModuleCohomologyFMapData.map_zero_augmentation {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app G) ≫
      D.map 0 =
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
      (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F)
```

## New

The signature is identical to the original signature above, with a complete proof and two
proved private helpers. No additional public declaration is introduced.

```lean
theorem ModuleCohomologyFMapData.map_zero_augmentation {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app G) ≫
      D.map 0 =
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
      (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none on refreshed base | none | Restored proved interface; no adaptation required. |

A source search on the refreshed base finds no import or use of this module or theorem.
The assigned node originally supported the degree-zero clause of
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`; that module on the refreshed
base has an unsplit proof and does not import this result. Its statement is unchanged.

## Status

landed 20261012T184324-L-4011983 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation)
