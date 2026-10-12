# AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map_target_naturality

## Reason

The return asks to take the current file and reapply the proof. The current repository
and server both lack the assigned module and node. Restore the assigned signature,
using the current ModuleCohomologyFMapFunctorial interface rather than the superseded
split-off modules. No existing interface or definition changes. No forced adaptation.

## Old

Absent on the current base. The assigned signature, formerly with `by sorry`, was:

```lean
theorem ModuleCohomologyFMapData.map_target_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf}
    {F F' : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (b : F ⟶ F')
    (D : ModuleCohomologyFMapData h G F φ)
    (E : ModuleCohomologyFMapData h G F' (φ ≫ (pushforward h).map b)) (p : ℕ) :
    D.map p ≫ (forget₂ _ AddCommGrpCat.{u}).map
        ((X.toRingedSpace.moduleCohomology p).map b) = E.map p
```

## New

The identical signature above has a complete Lean proof. Independence identifies D
and E with the respective canonical choices; existing canonical target naturality
finishes. No new sorry is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| none on current base | none | Restore the proved interface; no adaptation. |

A repository search finds no current import or use of the restored module or theorem.
The existing functoriality module provides both ingredients and does not import this
module, so this route creates no import cycle. Target statements are unchanged.

## Status

landed 20261012T202236-L-703312 2026-10-12 (merge of deliver/E2/Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataTargetNaturality)
