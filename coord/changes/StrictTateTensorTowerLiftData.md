# StrictTateTensorTowerPre and cocycle declarations

## Reason

The strict quotient construction is split into a pre-tower record and its
cocycle theorem so the item can assemble the final `AdicTower` with a complete
proof. These are new public declarations required by the item proof.

## Old

No declarations existed in the library.

## New

`StrictTateTensorTowerPre`, `StrictTateTensorTowerPre.Cocycle`,
`StrictTateTensorTowerPre.toAdicTower`, `strictTateTensorTower_pre`, and
`strictTateTensorTower_pre_cocycle` in the two new Sheaf modules.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StrictTateTensorTowerLiftData | C4 | imports the new modules and assembles the final AdicTower |
| Sheaf.Paper.StrictTateTensorTowerLift | unclaimed | imports the item module; sees the unchanged item theorem |

## Status

landed 20261027T233829-L-4121267 2026-10-27 (merge of deliver/C4/Sheaf.Paper.StrictTateTensorTowerLiftData)
