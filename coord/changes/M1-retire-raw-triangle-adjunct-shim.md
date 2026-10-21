# Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct

## Reason

The queue classifies this item as `retire` (coord/queue.tsv), and
coord/retire-items.tsv explicitly requests retirement of this Sheaf twin in favor of
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct`.
The current Sheaf source is a declaration-free public re-export of that upstream module.
The former consumer `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore`
is itself now a re-export of its upstream twin, whose proof imports the upstream adjunct
directly. No current Lean source imports the Sheaf adjunct shim.

The DAG node `sbc-lem-module-raw-triangle-adjunct` already records the canonical upstream
module and theorem. Its parent `sbc-lem-higher-image-raw-transition-to-hom-core` still uses
that theorem, whose complete upstream proof is retained. The unit route is unchanged.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct

/-! # Canonical upstream raw cohomology comparison

Source: Stacks Project, Tags 03Q8 and 09Z1.
This compatibility module exports the upstream `HigherDirectImageRawTriangleAdjunct`.
-/

@[expose] public section
```

## New

Withdraw the declaration-free Sheaf shim via `deleted.txt`. The delivery tool lands an
empty module at its old path. All upstream declarations, proofs, public imports and DAG
attachments are retained verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore | unclaimed | Historical inventory consumer; current source directly re-exports its upstream twin and requires no edit. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore | unclaimed | Already imports the canonical upstream adjunct directly; no edit. |

There are no current direct or transitive Lean importers of the withdrawn Sheaf shim.
No existing signature or definition changes.

## Status

landed 20261021T004834-L-1792936 2026-10-21 (merge of deliver/M1/Sheaf.AlgebraicGeometry.HigherDirectImageRawTriangleAdjunct)
