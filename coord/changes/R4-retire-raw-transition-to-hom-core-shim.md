# Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore

## Reason

The item's current queue row is `retire`, and `coord/retire-items.tsv` names the
canonical replacement as
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore`.
The Sheaf file is now a declaration-free public re-export of that exact upstream
module, following the independently reviewed D2 canonicalization landing.
Retiring this shim completes the inventory request against the current source.

The inventory's historical consumer,
`Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom`, now directly
re-exports its own upstream twin. That upstream twin imports the upstream core.
A search of all current Lean sources finds no import of the retiring Sheaf shim;
`tools/downstream.py` reports zero downstream modules.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore

/-! # Canonical upstream raw cohomology comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
This compatibility module exports the upstream `HigherDirectImageRawTransitionToHomCore`.
-/

@[expose] public section
```

## New

Withdraw the redundant Sheaf re-export with `deleted.txt`; the delivery tool
lands an empty module at this path. Retain the canonical upstream core and its
complete proof verbatim, including its public imports and private dependencies.

The node `sbc-lem-higher-image-raw-transition-to-hom-core` already points to the
upstream module and declaration. Only its Lean attachment's explanatory note is
updated to record retirement of the shim. Its statement, proof, proof dependencies
and unit are unchanged. No mathematical definition, signature or target changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom | unclaimed | Historical inventory consumer; now re-exports its upstream twin directly, so no edit. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom | unclaimed | Imports the canonical upstream core directly; no edit. |

There are zero current direct or transitive Lean consumers of the retired shim.
The core node remains attached to the proved canonical declaration. Searching
all DAG nodes and units for the core node id finds only its own node; its owning
unit `sk-lem-failure-field` has no realized entry requiring this Sheaf path.
No matching rework or return entry exists, and no quarantined source is withdrawn.

## Status

landed 20261021T011032-L-2030602 2026-10-21 (merge of deliver/R4/Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore)
