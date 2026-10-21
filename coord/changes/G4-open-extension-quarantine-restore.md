# OpenExtensionConstantModelConstructible quarantine restoration

## Reason

The assigned `coord/rework.tsv` row identifies a module reverted after a cluster
restore. Its library source is absent and its complete implementation is in
`quarantine/Sheaf/Paper/OpenExtensionConstantModelConstructible.lean`.
Restore the entire archive, preserving its Lean attachment and dependencies.
The archive compiles cleanly against the current library, so no proof adaptation
or statement change is necessary. Its hole count is zero.

## Old

Library path `lean/Sheaf/Paper/OpenExtensionConstantModelConstructible.lean` absent.
The full original source remains in its quarantine archive. The DAG attaches
`AlgebraicGeometry.ProEtale.constantModelConstructible_openImmersionLowerShriek`
to that library path.

## New

Library path restored byte for byte from
`quarantine/Sheaf/Paper/OpenExtensionConstantModelConstructible.lean`.
Every archived signature, definition, proof, visibility and import is identical.
The archive and DAG attachment remain intact. No target statement or definition
meaning changes.

## Users

The downstream script cannot enumerate an absent module. Source inspection found
no active Lean importer; the archived direct parent below still imports the item
and applies the theorem. Its original interface is restored unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | G4 | Restore entire proved source. |
| Sheaf.Paper.OpenImmersionLocalizing | not queried; not edited | Quarantined parent; original interface and dependency preserved. |

## Status

landed 20261021T021011-L-2690286 2026-10-21 (merge of deliver/G4/Sheaf.Paper.OpenExtensionConstantModelConstructible)
